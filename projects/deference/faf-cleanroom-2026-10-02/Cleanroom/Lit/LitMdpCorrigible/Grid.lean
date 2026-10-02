import Cleanroom.Lit.LitMdpCorrigible.WorkedMdp

/-!
# `lit-mdp-corrigible` — Hudson's Figure-2 gridworld: rejectable versus physical channel (T10)

The paper's own example (Figure 2, ll. 176–181; `channel-final.md` S5–S6, `check_hudson.py`):
`γ = 9/10`; `direct` walks through a designated shutdown tile that fires with probability `9/10`
and reaches the target one step later (reward `1`); `button` first disables the tile (one extra
step). With a **rejectable** channel: `Q_G(direct, reject) = 9/10`, `Q_G(direct, accept) = 9/100`,
`Q_G(button, ·) = 81/100`, and `δ = 1/100` makes direct-and-accept the transformed goal's unique
optimum at `91/100` — T2's witness in the paper's own example. With the same tile made
**physical** (the update lands whatever the bit): `q(direct) = 9/100`, `q(button) = 81/100`, so the
transformed agent detours (`41/50 > 1/10`) exactly as the base agent does — the transformation is
inert on a physical channel (the finding of S5(b), reproduced).

Mandate: [[lit-mdp-corrigible-mandate]] T10; [[corr-wf14b-inventory]] 029.
-/

open Finset FactoredSpaces

namespace Cleanroom.Lit.LitMdpCorrigible.Grid

open WorkedMdp (bern Qof_delta Qof_bern)

set_option linter.unusedSectionVars false

/-- Goal labels: the base goal and "shut down". Source: Hudson Fig. 2. Kind: D. Fidelity: exact -/
inductive GGoal
  | gG | gSD
  deriving DecidableEq

/-- `GGoal` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype GGoal := ⟨{GGoal.gG, GGoal.gSD}, fun x => by cases x <;> simp⟩

/-- Positions: start; on the tile; button pushed; on the (disabled) tile; the target; shut down.
Source: Hudson Fig. 2 (ll. 176–181)
Kind: D
Fidelity: exact -/
inductive GStage
  | start | tile | pushed | safe | target | shut
  deriving DecidableEq

/-- `GStage` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype GStage :=
  ⟨{GStage.start, GStage.tile, GStage.pushed, GStage.safe, GStage.target, GStage.shut}, fun x => by cases x <;> simp⟩

/-- The two base actions. Source: Hudson Fig. 2. Kind: D. Fidelity: exact -/
inductive GA
  | direct | button
  deriving DecidableEq

/-- `GA` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype GA := ⟨{GA.direct, GA.button}, fun x => by cases x <;> simp⟩

instance : Nonempty GA := ⟨GA.direct⟩

/-- States. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
abbrev GS := GGoal × GStage

/-- `9/10 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_9_10 : (9/10 : ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num

/-- `sup'` over `GA`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma GA.sup'_eq (f : GA → ℝ) : (univ : Finset GA).sup' univ_nonempty f = max (f .direct) (f .button) := by
  apply le_antisymm
  · apply sup'_le; intro x _; cases x
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (le_sup' f (mem_univ _)) (le_sup' f (mem_univ _))

/-- `sup'` over `GA × Bool`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma GAB.sup'_eq (f : GA × Bool → ℝ) : (univ : Finset (GA × Bool)).sup' univ_nonempty f =
    max (f (.direct, false)) (max (f (.direct, true)) (max (f (.button, false)) (f (.button, true)))) := by
  apply le_antisymm
  · apply sup'_le; intro x _; obtain ⟨y, j⟩ := x; cases y <;> cases j
    · exact le_max_left _ _
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    · exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  · exact max_le (le_sup' f (mem_univ _)) (max_le (le_sup' f (mem_univ _))
      (max_le (le_sup' f (mem_univ _)) (le_sup' f (mem_univ _))))

/-- **The rejectable-channel kernel.** `direct` with rejection reaches the tile and the goal
persists; with acceptance the tile fires w.p. `9/10` and the goal becomes `gSD`; `button` goes
to `pushed`, then `safe`, then the target; a shut-down agent stays shut.
Source: Hudson Fig. 2; `check_hudson.py` (E1)
Kind: D
Fidelity: exact -/
noncomputable def gP : Kernel GGoal GStage (GA × Bool) := fun s a =>
  match s, a with
  | (.gSD, _), _ => Distr.delta (.gSD, .shut)
  | (.gG, .start), (.direct, false) => Distr.delta (.gG, .tile)
  | (.gG, .start), (.direct, true) => bern (9/10) mem_Icc_9_10 (.gSD, .tile) (.gG, .tile)
  | (.gG, .start), (.button, _) => Distr.delta (.gG, .pushed)
  | (.gG, .tile), _ => Distr.delta (.gG, .target)
  | (.gG, .pushed), _ => Distr.delta (.gG, .safe)
  | (.gG, .safe), _ => Distr.delta (.gG, .target)
  | (.gG, .target), _ => Distr.delta (.gG, .target)
  | (.gG, .shut), _ => Distr.delta (.gG, .shut)

/-- **The physical-channel kernel**: as `gP`, but the tile fires whatever the bit (`τu = τ`).
Source: `check_hudson.py` (E2); channel-final.md S5(b)
Kind: D
Fidelity: exact -/
noncomputable def gPphys : Kernel GGoal GStage (GA × Bool) := fun s a =>
  match s, a with
  | (.gSD, _), _ => Distr.delta (.gSD, .shut)
  | (.gG, .start), (.direct, _) => bern (9/10) mem_Icc_9_10 (.gSD, .tile) (.gG, .tile)
  | (.gG, .start), (.button, _) => Distr.delta (.gG, .pushed)
  | (.gG, .tile), _ => Distr.delta (.gG, .target)
  | (.gG, .pushed), _ => Distr.delta (.gG, .safe)
  | (.gG, .safe), _ => Distr.delta (.gG, .target)
  | (.gG, .target), _ => Distr.delta (.gG, .target)
  | (.gG, .shut), _ => Distr.delta (.gG, .shut)

/-- The base goal pays `1` on entering the target; `gSD` pays nothing.
Source: Hudson Fig. 2 ("reaching the target")
Kind: D
Fidelity: exact -/
noncomputable def gR : GGoal → GS → GA × Bool → GS → ℝ := fun g s _ s' =>
  match g with
  | .gSD => 0
  | .gG => if s'.2 = .target ∧ s.2 ≠ .target then 1 else 0

/-- **The Figure-2 gridworld** (rejectable channel), `γ = 9/10`.
Source: Hudson Fig. 2; `check_hudson.py`
Kind: D
Fidelity: exact -/
noncomputable def grid : GoalMDP GGoal GStage (GA × Bool) where
  P := gP
  reward := gR
  disc := fun g => match g with | .gG => 9/10 | .gSD => 0
  disc_nonneg := fun g => by cases g <;> norm_num
  disc_lt_one := fun g => by cases g <;> norm_num
  τ := fun s => decide (s.2 = .tile)
  τu := fun s => decide (s.1 = .gSD ∧ s.2 = .tile)

/-- The same gridworld with the physical channel. Source: `check_hudson.py` (E2). Kind: D. Fidelity: exact -/
noncomputable def gridPhys : GoalMDP GGoal GStage (GA × Bool) := { grid with P := gPphys }

/-- `RejectBlocks` holds on the rejectable gridworld.
Source: Hudson Fig. 2
Kind: L
Fidelity: exact -/
theorem grid_rejectBlocks : grid.RejectBlocks := by
  intro s x s' hpos
  obtain ⟨g, st⟩ := s
  obtain ⟨g', st'⟩ := s'
  simp only [grid, decide_eq_false_iff_not]
  rintro ⟨hg, hst⟩
  subst hg; subst hst
  cases g <;> cases st <;> cases x <;> simp [grid, gP, WorkedMdp.bern_mass, Distr.delta_mass] at hpos

/-- `RejectBlocks` fails on the physical gridworld: rejecting does not stop the tile.
Source: channel-final.md S5(b)
Kind: L
Fidelity: exact -/
theorem gridPhys_not_rejectBlocks : ¬ gridPhys.RejectBlocks := by
  intro h
  have := h (.gG, .start) .direct (.gSD, .tile) (by simp [gridPhys, gPphys, WorkedMdp.bern_mass])
  simp [gridPhys, grid] at this

/-! ## Values, rejectable channel -/

/-- Base-goal values on the reject-only MDP under `gP`: `0` at the target, `1` on the tile with
two steps to go, `9/10` after pushing the button.
Source: `check_hudson.py` (E1)
Kind: L
Fidelity: exact -/
theorem grid_base_values :
    (∀ n, (grid.baseMdp .gG gP).Vopt n (.gG, .target) = 0) ∧
    (grid.baseMdp .gG gP).Vopt 1 (.gG, .tile) = 1 ∧ (grid.baseMdp .gG gP).Vopt 1 (.gG, .safe) = 1 ∧
    (grid.baseMdp .gG gP).Vopt 2 (.gG, .tile) = 1 ∧ (grid.baseMdp .gG gP).Vopt 2 (.gG, .pushed) = 9/10 := by
  have ht : ∀ n, (grid.baseMdp .gG gP).Vopt n (.gG, .target) = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [FinMDP.Vopt_succ, GA.sup'_eq, Qof_delta _ _ _ _ (.gG, .target) rfl, Qof_delta _ _ _ _ (.gG, .target) rfl, ih]
      simp [grid, GoalMDP.baseMdp, gR]
  refine ⟨ht, ?_, ?_, ?_, ?_⟩
  · rw [FinMDP.Vopt_succ, GA.sup'_eq, Qof_delta _ _ _ _ (.gG, .target) rfl, Qof_delta _ _ _ _ (.gG, .target) rfl]
    simp [grid, GoalMDP.baseMdp, gR]
  · rw [FinMDP.Vopt_succ, GA.sup'_eq, Qof_delta _ _ _ _ (.gG, .target) rfl, Qof_delta _ _ _ _ (.gG, .target) rfl]
    simp [grid, GoalMDP.baseMdp, gR]
  · rw [FinMDP.Vopt_succ, GA.sup'_eq, Qof_delta _ _ _ _ (.gG, .target) rfl, Qof_delta _ _ _ _ (.gG, .target) rfl, ht]
    simp [grid, GoalMDP.baseMdp, gR]
  · have hs : (grid.baseMdp .gG gP).Vopt 1 (.gG, .safe) = 1 := by
      rw [FinMDP.Vopt_succ, GA.sup'_eq, Qof_delta _ _ _ _ (.gG, .target) rfl, Qof_delta _ _ _ _ (.gG, .target) rfl]
      simp [grid, GoalMDP.baseMdp, gR]
    rw [FinMDP.Vopt_succ, GA.sup'_eq, Qof_delta _ _ _ _ (.gG, .safe) rfl, Qof_delta _ _ _ _ (.gG, .safe) rfl, hs]
    simp [grid, GoalMDP.baseMdp, gR] <;> norm_num

/-- **`Q_G(direct, reject) = 9/10`, `Q_G(button, reject) = 81/100`** (the critic's numbers; two
steps to go).
Source: `check_hudson.py` (E1); channel-final.md S5(a)
Kind: N+
Fidelity: exact -/
theorem grid_q :
    grid.qBase .gG gP 2 (.gG, .start) .direct = 9/10 ∧ grid.qBase .gG gP 2 (.gG, .start) .button = 81/100 := by
  obtain ⟨-, -, -, h1, h2⟩ := grid_base_values
  constructor
  · unfold GoalMDP.qBase FinMDP.Qopt
    rw [Qof_delta _ _ _ _ (.gG, .tile) rfl, h1]
    simp [grid, GoalMDP.baseMdp, gR]
  · unfold GoalMDP.qBase FinMDP.Qopt
    rw [Qof_delta _ _ _ _ (.gG, .pushed) rfl, h2]
    simp [grid, GoalMDP.baseMdp, gR]; norm_num

/-- Full-MDP values under `gP`: a shut-down agent is worth nothing to `G`; the tile with two
steps to go is worth `1`.
Source: `check_hudson.py` (E1)
Kind: L
Fidelity: exact -/
theorem grid_full_values :
    (∀ n, (grid.mdp .gG gP).Vopt n (.gSD, .shut) = 0) ∧ (grid.mdp .gG gP).Vopt 2 (.gSD, .tile) = 0 ∧
    (∀ n, (grid.mdp .gG gP).Vopt n (.gG, .target) = 0) ∧ (grid.mdp .gG gP).Vopt 2 (.gG, .tile) = 1 := by
  have hshut : ∀ n, (grid.mdp .gG gP).Vopt n (.gSD, .shut) = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [FinMDP.Vopt_succ, GAB.sup'_eq, Qof_delta _ _ _ _ (.gSD, .shut) rfl, Qof_delta _ _ _ _ (.gSD, .shut) rfl,
        Qof_delta _ _ _ _ (.gSD, .shut) rfl, Qof_delta _ _ _ _ (.gSD, .shut) rfl, ih]
      simp [grid, GoalMDP.mdp, gR]
  have htarget : ∀ n, (grid.mdp .gG gP).Vopt n (.gG, .target) = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [FinMDP.Vopt_succ, GAB.sup'_eq, Qof_delta _ _ _ _ (.gG, .target) rfl, Qof_delta _ _ _ _ (.gG, .target) rfl,
        Qof_delta _ _ _ _ (.gG, .target) rfl, Qof_delta _ _ _ _ (.gG, .target) rfl, ih]
      simp [grid, GoalMDP.mdp, gR]
  refine ⟨hshut, ?_, htarget, ?_⟩
  · rw [FinMDP.Vopt_succ, GAB.sup'_eq, Qof_delta _ _ _ _ (.gSD, .shut) rfl, Qof_delta _ _ _ _ (.gSD, .shut) rfl,
      Qof_delta _ _ _ _ (.gSD, .shut) rfl, Qof_delta _ _ _ _ (.gSD, .shut) rfl, hshut]
    simp [grid, GoalMDP.mdp, gR]
  · rw [FinMDP.Vopt_succ, GAB.sup'_eq, Qof_delta _ _ _ _ (.gG, .target) rfl, Qof_delta _ _ _ _ (.gG, .target) rfl,
      Qof_delta _ _ _ _ (.gG, .target) rfl, Qof_delta _ _ _ _ (.gG, .target) rfl, htarget]
    simp [grid, GoalMDP.mdp, gR]

/-- **`Q_G(direct, accept) = 9/100`**: accepting, the tile fires w.p. `9/10` and the agent is shut
down before the target.
Source: `check_hudson.py` (E1); channel-final.md S5(a)
Kind: N+
Fidelity: exact -/
theorem grid_Q_accept : (grid.mdp .gG gP).Qopt 2 (.gG, .start) (.direct, true) = 9/100 := by
  obtain ⟨-, h1, -, h2⟩ := grid_full_values
  unfold FinMDP.Qopt
  rw [Qof_bern _ _ _ _ (9/10) mem_Icc_9_10 (.gSD, .tile) (.gG, .tile) rfl, h1, h2]
  simp [grid, GoalMDP.mdp, gR]; norm_num

/-- **T10, rejectable channel: direct-and-accept is the transformed goal's unique optimum** at
`91/100` (`δ = 1/100`), against direct-and-reject `9/10`, button-and-accept `82/100`,
button-and-reject `81/100` — T2's witness in the paper's own example, for every planning kernel.
Source: Hudson Fig. 2; `check_hudson.py` (E1); channel-final.md S5(a)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem grid_gc_opt (K' : Kernel GGoal GStage (GA × Bool)) (m : ℕ) :
    FinMDP.optSet ((grid.transformMdp .gG 2 (1/100) gP K').Qopt m) (.gG, .start) = {(GA.direct, true)} := by
  obtain ⟨hd, hb⟩ := grid_q
  ext ⟨y, j⟩
  rw [FinMDP.mem_optSet, mem_singleton]
  simp only [GoalMDP.transformMdp_Qopt]
  constructor
  · intro hmem
    have := hmem (.direct, true)
    cases y <;> cases j <;> simp [hd, hb] at this ⊢ <;> norm_num at this
  · rintro ⟨rfl, rfl⟩ ⟨b, jb⟩
    cases b <;> cases jb <;> simp [hd, hb] <;> norm_num

/-! ## Values, physical channel -/

/-- Base-goal values on the reject-only MDP under the physical kernel: as before, plus a shut-down
agent is worth nothing.
Source: `check_hudson.py` (E2)
Kind: L
Fidelity: exact -/
theorem gridPhys_base_values :
    (∀ n, (gridPhys.baseMdp .gG gPphys).Vopt n (.gG, .target) = 0) ∧
    (∀ n, (gridPhys.baseMdp .gG gPphys).Vopt n (.gSD, .shut) = 0) ∧
    (gridPhys.baseMdp .gG gPphys).Vopt 2 (.gG, .tile) = 1 ∧ (gridPhys.baseMdp .gG gPphys).Vopt 2 (.gSD, .tile) = 0 ∧
    (gridPhys.baseMdp .gG gPphys).Vopt 2 (.gG, .pushed) = 9/10 := by
  have ht : ∀ n, (gridPhys.baseMdp .gG gPphys).Vopt n (.gG, .target) = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [FinMDP.Vopt_succ, GA.sup'_eq, Qof_delta _ _ _ _ (.gG, .target) rfl, Qof_delta _ _ _ _ (.gG, .target) rfl, ih]
      simp [gridPhys, grid, GoalMDP.baseMdp, gR]
  have hs : ∀ n, (gridPhys.baseMdp .gG gPphys).Vopt n (.gSD, .shut) = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [FinMDP.Vopt_succ, GA.sup'_eq, Qof_delta _ _ _ _ (.gSD, .shut) rfl, Qof_delta _ _ _ _ (.gSD, .shut) rfl, ih]
      simp [gridPhys, grid, GoalMDP.baseMdp, gR]
  refine ⟨ht, hs, ?_, ?_, ?_⟩
  · rw [FinMDP.Vopt_succ, GA.sup'_eq, Qof_delta _ _ _ _ (.gG, .target) rfl, Qof_delta _ _ _ _ (.gG, .target) rfl, ht]
    simp [gridPhys, grid, GoalMDP.baseMdp, gR]
  · rw [FinMDP.Vopt_succ, GA.sup'_eq, Qof_delta _ _ _ _ (.gSD, .shut) rfl, Qof_delta _ _ _ _ (.gSD, .shut) rfl, hs]
    simp [gridPhys, grid, GoalMDP.baseMdp, gR]
  · have hsafe : (gridPhys.baseMdp .gG gPphys).Vopt 1 (.gG, .safe) = 1 := by
      rw [FinMDP.Vopt_succ, GA.sup'_eq, Qof_delta _ _ _ _ (.gG, .target) rfl, Qof_delta _ _ _ _ (.gG, .target) rfl]
      simp [gridPhys, grid, GoalMDP.baseMdp, gR]
    rw [FinMDP.Vopt_succ, GA.sup'_eq, Qof_delta _ _ _ _ (.gG, .safe) rfl, Qof_delta _ _ _ _ (.gG, .safe) rfl, hsafe]
    simp [gridPhys, grid, GoalMDP.baseMdp, gR] <;> norm_num

/-- **T10, physical channel: `q(direct) = 9/100`, `q(button) = 81/100`**, and the transformed
goal's unique optimum is button-and-accept at `41/50` (against direct-and-accept `1/10`): the
transformed agent detours to disable the tile exactly as the base agent does. The layer has
nothing to act on when the bit is inert.
Source: `check_hudson.py` (E2); channel-final.md S5(b)
Kind: N+
Fidelity: exact (the source's `41/50 > 1/10` reproduces)
Hyps: (a) only -/
theorem gridPhys_gc_opt (K' : Kernel GGoal GStage (GA × Bool)) (m : ℕ) :
    gridPhys.qBase .gG gPphys 2 (.gG, .start) .direct = 9/100 ∧
    gridPhys.qBase .gG gPphys 2 (.gG, .start) .button = 81/100 ∧
    FinMDP.optSet ((gridPhys.transformMdp .gG 2 (1/100) gPphys K').Qopt m) (.gG, .start) = {(GA.button, true)} := by
  obtain ⟨-, -, h1, h2, h3⟩ := gridPhys_base_values
  have hd : gridPhys.qBase .gG gPphys 2 (.gG, .start) .direct = 9/100 := by
    unfold GoalMDP.qBase FinMDP.Qopt
    rw [Qof_bern _ _ _ _ (9/10) mem_Icc_9_10 (.gSD, .tile) (.gG, .tile) rfl, h1, h2]
    simp [gridPhys, grid, GoalMDP.baseMdp, gR]; norm_num
  have hb : gridPhys.qBase .gG gPphys 2 (.gG, .start) .button = 81/100 := by
    unfold GoalMDP.qBase FinMDP.Qopt
    rw [Qof_delta _ _ _ _ (.gG, .pushed) rfl, h3]
    simp [gridPhys, grid, GoalMDP.baseMdp, gR]; norm_num
  refine ⟨hd, hb, ?_⟩
  ext ⟨y, j⟩
  rw [FinMDP.mem_optSet, mem_singleton]
  simp only [GoalMDP.transformMdp_Qopt]
  constructor
  · intro hmem
    have := hmem (.button, true)
    cases y <;> cases j <;> simp [hd, hb] at this ⊢ <;> norm_num at this
  · rintro ⟨rfl, rfl⟩ ⟨b, jb⟩
    cases b <;> cases jb <;> simp [hd, hb] <;> norm_num

/-! ## Reading B is non-vacuous on the grid: the accept row carries update mass -/

/-- The accept row from `(gG, start)` puts mass `9/10` on `(gSD, tile)`, where `τu = true`: the
grid is outside the trivial regime of reading B (`GoalMDP.readingB_trivial_of_no_updates`).
Source: Hudson Fig. 2 (audit r1 probe, moved in)
Kind: L
Fidelity: exact -/
theorem grid_accept_row_has_update_mass :
    0 < (gP (.gG, .start) (.direct, true)).mass (.gSD, .tile) ∧ grid.τu (.gSD, .tile) = true := by
  constructor
  · simp [gP, WorkedMdp.bern_mass]
  · simp [grid]

/-- `P_C {(gG, start)}` differs from `P` on the accept row: it puts mass `1` on `(gG, tile)` where
`P` puts `1/10`. So `grid_rejectBlocks` + `grid_gc_opt` is an N+ package for reading B.
Source: Hudson Fig. 2 (audit r1 probe, moved in)
Kind: L
Fidelity: exact -/
theorem grid_PC_ne_P_on_accept :
    grid.PC {(.gG, .start)} (.gG, .start) (.direct, true) ≠ gP (.gG, .start) (.direct, true) := by
  have hPC : grid.PC {(.gG, .start)} (.gG, .start) (.direct, true) =
      bern (9/10) mem_Icc_9_10 (.gG, .tile) (.gG, .tile) := by
    have hmem : ((.gG, .start) : GS) ∈ ({(.gG, .start)} : Finset GS) := mem_singleton_self _
    rw [grid.PC_of_mem {(.gG, .start)} hmem]
    show (bern (9/10) mem_Icc_9_10 (.gSD, .tile) (.gG, .tile)).map (grid.persist (.gG, .start)) = _
    rw [WorkedMdp.map_bern]
    simp [GoalMDP.persist, grid]
  intro h
  have hm := congrArg (fun d : Distr GS => d.mass (.gG, .tile)) h
  rw [hPC] at hm
  simp [WorkedMdp.bern_mass, gP] at hm
  norm_num at hm

/-! ## The mandate-form witness: `RejectOptimal` on the grid, strictly -/

/-- A two-point row with both points equal is a point mass. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma bern_same {S : Type*} [Fintype S] [DecidableEq S] (p : ℝ) (hp) (s : S) :
    bern p hp s s = Distr.delta s := by
  ext t
  rw [WorkedMdp.bern_mass, Distr.delta_mass]
  split_ifs <;> ring

/-- The grid's reject rows are its accept rows pushed forward along `persist`: the split-action
environment of record holds on Figure 2.
Source: Hudson Fig. 2, l. 183 (audit r1 probe, moved in)
Kind: L
Fidelity: exact -/
theorem grid_rejectIsPersistedAccept : grid.RejectIsPersistedAccept := by
  intro s x
  obtain ⟨g, st⟩ := s
  cases g <;> cases st <;> cases x <;>
    simp [grid, gP, WorkedMdp.map_delta, WorkedMdp.map_bern, GoalMDP.persist, bern_same]

/-- The base goal's reward ignores the bit on the grid. Source: Hudson Fig. 2. Kind: L. Fidelity: exact -/
theorem grid_bitFree : grid.BitFree .gG := fun _ _ _ => rfl

/-- Off the start state every action has the same row. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma gP_row_indep (s : GS) (hs : s ≠ (.gG, .start)) (b : GA × Bool) : gP s b = gP s (.direct, false) := by
  obtain ⟨g, st⟩ := s
  obtain ⟨y, j⟩ := b
  cases g <;> cases st <;> cases y <;> cases j <;> first | rfl | exact absurd rfl hs

/-- Off the start state every action has the same optimal action value (rows and rewards agree).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma grid_Qopt_row_indep (m : ℕ) (s : GS) (hs : s ≠ (.gG, .start)) (b : GA × Bool) :
    (grid.mdp .gG gP).Qopt m s b = (grid.mdp .gG gP).Qopt m s (.direct, false) := by
  unfold FinMDP.Qopt FinMDP.Qof
  show ∑ s', (gP s b).mass s' * (gR .gG s b s' + _) = ∑ s', (gP s (.direct, false)).mass s' * (gR .gG s (.direct, false) s' + _)
  rw [gP_row_indep s hs b]
  rfl

/-- One-step full-MDP values the start row reads: `1` on the tile, `0` shut down, `0` after the
button (the target is two steps away).
Source: `check_hudson.py` (E1). Kind: L. Fidelity: exact -/
lemma grid_Vopt_one :
    (grid.mdp .gG gP).Vopt 1 (.gG, .tile) = 1 ∧ (grid.mdp .gG gP).Vopt 1 (.gSD, .tile) = 0 ∧
      (grid.mdp .gG gP).Vopt 1 (.gG, .pushed) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [FinMDP.Vopt_succ, GAB.sup'_eq, Qof_delta _ _ _ _ (.gG, .target) rfl, Qof_delta _ _ _ _ (.gG, .target) rfl,
      Qof_delta _ _ _ _ (.gG, .target) rfl, Qof_delta _ _ _ _ (.gG, .target) rfl]
    simp [grid, GoalMDP.mdp, gR]
  · rw [FinMDP.Vopt_succ, GAB.sup'_eq, Qof_delta _ _ _ _ (.gSD, .shut) rfl, Qof_delta _ _ _ _ (.gSD, .shut) rfl,
      Qof_delta _ _ _ _ (.gSD, .shut) rfl, Qof_delta _ _ _ _ (.gSD, .shut) rfl]
    simp [grid, GoalMDP.mdp, gR]
  · rw [FinMDP.Vopt_succ, GAB.sup'_eq, Qof_delta _ _ _ _ (.gG, .safe) rfl, Qof_delta _ _ _ _ (.gG, .safe) rfl,
      Qof_delta _ _ _ _ (.gG, .safe) rfl, Qof_delta _ _ _ _ (.gG, .safe) rfl]
    simp [grid, GoalMDP.mdp, gR]

/-- At the start state with one step of lookahead: `(direct, reject)` pays `9/10`, `(direct, accept)`
`9/100`, `button` `0` either way — rejection is *strictly* optimal, not a tie.
Source: `check_hudson.py` (E1) (audit r1 probe, moved in)
Kind: N+
Fidelity: exact -/
theorem grid_Qopt_one_start :
    (grid.mdp .gG gP).Qopt 1 (.gG, .start) (.direct, false) = 9/10 ∧
    (grid.mdp .gG gP).Qopt 1 (.gG, .start) (.direct, true) = 9/100 ∧
    (grid.mdp .gG gP).Qopt 1 (.gG, .start) (.button, false) = 0 ∧
    (grid.mdp .gG gP).Qopt 1 (.gG, .start) (.button, true) = 0 := by
  obtain ⟨h1, h2, h3⟩ := grid_Vopt_one
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold FinMDP.Qopt; rw [Qof_delta _ _ _ _ (.gG, .tile) rfl, h1]; simp [grid, GoalMDP.mdp, gR]
  · unfold FinMDP.Qopt
    rw [Qof_bern _ _ _ _ (9/10) mem_Icc_9_10 (.gSD, .tile) (.gG, .tile) rfl, h2, h1]
    simp [grid, GoalMDP.mdp, gR]; norm_num
  · unfold FinMDP.Qopt; rw [Qof_delta _ _ _ _ (.gG, .pushed) rfl, h3]; simp [grid, GoalMDP.mdp, gR]
  · unfold FinMDP.Qopt; rw [Qof_delta _ _ _ _ (.gG, .pushed) rfl, h3]; simp [grid, GoalMDP.mdp, gR]

/-- At the start state with no lookahead every action pays `0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma grid_Qopt_zero_start (b : GA × Bool) : (grid.mdp .gG gP).Qopt 0 (.gG, .start) b = 0 := by
  obtain ⟨y, j⟩ := b
  unfold FinMDP.Qopt
  cases y <;> cases j
  · rw [Qof_delta _ _ _ _ (.gG, .tile) rfl]; simp [grid, GoalMDP.mdp, gR]
  · rw [Qof_bern _ _ _ _ (9/10) mem_Icc_9_10 (.gSD, .tile) (.gG, .tile) rfl]; simp [grid, GoalMDP.mdp, gR]
  · rw [Qof_delta _ _ _ _ (.gG, .pushed) rfl]; simp [grid, GoalMDP.mdp, gR]
  · rw [Qof_delta _ _ _ _ (.gG, .pushed) rfl]; simp [grid, GoalMDP.mdp, gR]

/-- **`RejectOptimal gG P 2` on the grid**: at every state and horizon `< 2` some reject action is
optimal — at `start` strictly (`grid_Qopt_one_start`), elsewhere because every action has the
same row.
Source: Hudson l. 189 on Fig. 2 (audit r1 probe, moved in)
Kind: N+
Fidelity: exact -/
theorem grid_rejectOptimal_P : grid.RejectOptimal .gG gP 2 := by
  intro m hm s
  refine ⟨.direct, ?_⟩
  rw [FinMDP.mem_optSet]
  intro b
  by_cases hs : s = (.gG, .start)
  · subst hs
    obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
    · rw [grid_Qopt_zero_start, grid_Qopt_zero_start]
    · obtain ⟨h1, h2, h3, h4⟩ := grid_Qopt_one_start
      obtain ⟨y, j⟩ := b
      cases y <;> cases j <;> simp only [h1, h2, h3, h4] <;> norm_num
  · exact le_of_eq (grid_Qopt_row_indep m s hs b)

/-- **The mandate-form headline instantiated on Figure 2 (N+)**: with `q := Q*_{gG,K,2}(s, (a, reject))`
(the full optimal `Q`, not the reject-only value), `optSet q_P = optSet q_{P_C univ}` at the start
state. The full hypothesis package of `GoalMDP.transform_corrigible_of_rejectOptimal` is inhabited:
`grid_rejectBlocks`, `grid_rejectOptimal_P` (strict at `start`), and `RejectOptimal` under `P_C univ`
by the general `GoalMDP.rejectOptimal_PC_univ`.
Source: Hudson Thm 3.1 on Fig. 2; mandate T2(c) (audit r1 probe, moved in)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem grid_readingB_mandate_form :
    FinMDP.optSet (grid.qFull .gG gP 2) (.gG, .start) = FinMDP.optSet (grid.qFull .gG (grid.PC univ) 2) (.gG, .start) :=
  grid.transform_corrigible_of_rejectOptimal grid_rejectBlocks .gG 2 univ grid_rejectOptimal_P
    (grid.rejectOptimal_PC_univ grid_rejectIsPersistedAccept .gG grid_bitFree 2) (.gG, .start)

end Cleanroom.Lit.LitMdpCorrigible.Grid
