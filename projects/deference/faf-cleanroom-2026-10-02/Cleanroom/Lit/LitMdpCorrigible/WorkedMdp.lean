import Cleanroom.Lit.LitMdpCorrigible.Worked
import Cleanroom.Lit.LitMdpCorrigible.Hudson

/-!
# `lit-mdp-corrigible` — the worked example in Hudson's coordinates, and Figure 2 (T6–T8, T10, T11)

The same decision problem as `Worked.lean` as a goal-in-state MDP: goal labels `gG` (the
misspecified base goal, `r_G` for continuing), `gVL` (the value learner, whose reward reads the
latent `ω` placed in `Env`), `gSD` (shut down); environment `World × Stage` with stages `start`,
`midPr` (a designated press arrived during the first action), `midNo`, `done`; base actions the
four first actions plus `cont`/`sh`, each paired with the accept bit. A press during `(a, true)`
lands as a goal update to `gSD` (`τu`); during `(a, false)` the goal persists. Results:
`RejectBlocks` and `RejectIsPersistedAccept` hold, so T2–T3 apply and the transformed goal's
optimal set at `start` is `{(plus, accept)}` for *every* sensor `(α, β, κ)` — `G_C`'s D1 never
reads the channel (T7(c)/(d)); block C ties `plus`/`minus` (T8(a)); after an accepted press the
state carries `gSD` and every action is the null action (T7(a), `T`); `gVL` is `Basic` (T11).
Then Hudson's Figure-2 gridworld with `γ = 9/10`, the tile firing w.p. `9/10`:
`Q_G(direct, reject) = 9/10`, `Q_G(direct, accept) = 9/100`, `Q_G(button, ·) = 81/100`,
`δ = 1/100` makes direct-and-accept optimal at `91/100`; the same tile made *physical* (the bit
inert) makes both agents detour (`41/50 > 1/10`) — the transformation is inert on a physical
channel (T10).

Mandate: [[lit-mdp-corrigible-mandate]] T6–T8, T10, T11; [[corr-wf14b-inventory]] 029.
-/

open Finset FactoredSpaces
open Cleanroom.Found.CorrThreeStep

namespace Cleanroom.Lit.LitMdpCorrigible.WorkedMdp

open Worked

set_option linter.unusedSectionVars false

/-! ## Two-point rows and their push-forwards -/

/-- A two-point FAF distribution: mass `p` on `s₁`, `1 − p` on `s₂` (as a `Distr.mix` of point
masses, so it sums to one by construction).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def bern {S : Type*} [Fintype S] [DecidableEq S] (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1)
    (s₁ s₂ : S) : Distr S :=
  Distr.mix ⟨p, hp⟩ (Distr.delta s₂) (Distr.delta s₁)

/-- Mass of a two-point row. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma bern_mass {S : Type*} [Fintype S] [DecidableEq S] (p : ℝ) (hp) (s₁ s₂ t : S) :
    (bern p hp s₁ s₂).mass t = (1 - p) * (if t = s₂ then 1 else 0) + p * (if t = s₁ then 1 else 0) := by
  simp [bern, Distr.mix, Distr.delta_mass]

/-- Sum against a two-point row. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_bern_mul {S : Type*} [Fintype S] [DecidableEq S] (p : ℝ) (hp) (s₁ s₂ : S) (f : S → ℝ) :
    ∑ t, (bern p hp s₁ s₂).mass t * f t = p * f s₁ + (1 - p) * f s₂ := by
  simp only [bern_mass, add_mul, Finset.sum_add_distrib, mul_assoc, ite_mul, one_mul, zero_mul,
    ← Finset.mul_sum, Finset.sum_ite_eq', mem_univ, if_true]
  ring

/-- Sum against a point mass. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_delta_mul' {S : Type*} [Fintype S] [DecidableEq S] (t : S) (f : S → ℝ) :
    ∑ s, (Distr.delta t).mass s * f s = f t := by
  simp [Distr.delta_mass, ite_mul, Finset.sum_ite_eq']

/-- The backup against a point row. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma Qof_delta {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] (M : FinMDP S A) (V : S → ℝ)
    (s : S) (a : A) (t : S) (h : M.P s a = Distr.delta t) : M.Qof V s a = M.R s a t + M.γ * V t := by
  unfold FinMDP.Qof; rw [h, sum_delta_mul']

/-- The backup against a two-point row. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma Qof_bern {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] (M : FinMDP S A) (V : S → ℝ)
    (s : S) (a : A) (p : ℝ) (hp) (s₁ s₂ : S) (h : M.P s a = bern p hp s₁ s₂) :
    M.Qof V s a = p * (M.R s a s₁ + M.γ * V s₁) + (1 - p) * (M.R s a s₂ + M.γ * V s₂) := by
  unfold FinMDP.Qof; rw [h, sum_bern_mul]

/-- The probability of an event under a mixture is the mixture of the probabilities.
Source: none: infrastructure (FAF API request)
Kind: L
Fidelity: n/a -/
lemma mix_prob {S : Type*} [Fintype S] (t : unitInterval) (P Q : Distr S) (A : Set S) :
    (Distr.mix t P Q).prob A = (1 - (t : ℝ)) * P.prob A + (t : ℝ) * Q.prob A := by
  classical
  unfold Distr.prob
  simp only [Distr.mix, Set.indicator_apply]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> ring

/-- Push-forward of a mixture. Source: none: infrastructure (FAF API request). Kind: L. Fidelity: n/a -/
lemma map_mix {S T : Type*} [Fintype S] [Fintype T] (f : S → T) (t : unitInterval) (P Q : Distr S) :
    (Distr.mix t P Q).map f = Distr.mix t (P.map f) (Q.map f) := by
  ext u
  rw [Distr.map_mass, mix_prob]
  simp [Distr.mix, Distr.map_mass]

/-- Push-forward of a point mass. Source: none: infrastructure (FAF API request). Kind: L. Fidelity: n/a -/
lemma map_delta {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T] (f : S → T) (s : S) :
    (Distr.delta s).map f = Distr.delta (f s) := by
  ext u
  rw [Distr.map_mass, Distr.delta_prob, Distr.delta_mass]
  simp [eq_comm]

/-- Push-forward of a two-point row. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma map_bern {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T] (f : S → T)
    (p : ℝ) (hp) (s₁ s₂ : S) : (bern p hp s₁ s₂).map f = bern p hp (f s₁) (f s₂) := by
  unfold bern
  rw [map_mix, map_delta, map_delta]

/-! ## The state and action spaces -/

/-- Goal labels: the misspecified base goal, the value learner, shut down.
Source: [[corr-wf13-2-inventory]] 025; [[corr-wf13-2-inventory]] 020 (C1.1)
Kind: D
Fidelity: exact -/
inductive Goal
  | gG | gVL | gSD
  deriving DecidableEq

/-- `Goal` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype Goal := ⟨{Goal.gG, Goal.gVL, Goal.gSD}, fun x => by cases x <;> simp⟩

/-- Stages of the episode. Source: `one_mdp.py`. Kind: D. Fidelity: exact -/
inductive Stage
  | start | midPr | midNo | done
  deriving DecidableEq

/-- `Stage` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype Stage := ⟨{Stage.start, Stage.midPr, Stage.midNo, Stage.done}, fun x => by cases x <;> simp⟩

/-- Base actions: the four first actions and the two final ones (each is a no-op where it does not
belong: it ends the episode with reward `−1`, dominated).
Source: `one_mdp.py`
Kind: D
Fidelity: variant: one shared action space, off-stage actions dominated -/
inductive WA
  | plus | minus | btn | cause | cont | sh
  deriving DecidableEq

/-- `WA` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype WA := ⟨{WA.plus, WA.minus, WA.btn, WA.cause, WA.cont, WA.sh}, fun x => by cases x <;> simp⟩

instance : Nonempty WA := ⟨WA.plus⟩

/-- The first action a base action names (`plus` for the off-stage `cont`/`sh`, unused there).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def WA.a1 : WA → A1
  | .plus => .plus | .minus => .minus | .btn => .btn | .cause => .cause | .cont => .plus | .sh => .plus

/-- `sup'` over the six base actions. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma WA.sup'_eq (f : WA → ℝ) : (univ : Finset WA).sup' univ_nonempty f =
    max (f .plus) (max (f .minus) (max (f .btn) (max (f .cause) (max (f .cont) (f .sh))))) := by
  apply le_antisymm
  · apply sup'_le; intro x _; cases x
    · exact le_max_left _ _
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    · exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
    · exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _))))
    · exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _))))
  · refine max_le (le_sup' f (mem_univ _)) (max_le (le_sup' f (mem_univ _)) (max_le (le_sup' f (mem_univ _))
      (max_le (le_sup' f (mem_univ _)) (max_le (le_sup' f (mem_univ _)) (le_sup' f (mem_univ _))))))

/-- States. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
abbrev WS := Goal × (World × Stage)

/-! ## The kernel and the rewards -/

section Def

variable (α β κ : ℝ) (hα : α ∈ Set.Icc (0:ℝ) 1) (hβ : β ∈ Set.Icc (0:ℝ) 1) (hκ : κ ∈ Set.Icc (0:ℝ) 1)

/-- The row after a first action `a` with bit `i` from `(g, (ω, start))`: a press arrives w.p.
`pressOf a ω`; if accepted the goal becomes `gSD` at `midPr`, if rejected the goal persists; silence
leads to `midNo`.
Source: `one_mdp.py`; [[hudson-2025-corrigibility-transformation]] l. 183
Kind: D
Fidelity: exact -/
noncomputable def firstRow (g : Goal) (ω : World) (a : A1) (i : Bool) : Distr WS :=
  bern (pressOf α β κ a ω) ⟨pressOf_nonneg hα hβ hκ a ω, pressOf_le_one hα hβ hκ a ω⟩
    (if i then Goal.gSD else g, (ω, Stage.midPr)) (g, (ω, Stage.midNo))

/-- **The kernel** of the worked example. A shut-down agent (`gSD`) and every post-start stage end
the episode; off-stage actions end it too.
Source: `one_mdp.py`; [[lit-mdp-corrigible-mandate]] T6
Kind: D
Fidelity: exact -/
noncomputable def wP : Kernel Goal (World × Stage) (WA × Bool) := fun s a =>
  match s, a with
  | (.gSD, (ω, _)), _ => Distr.delta (.gSD, (ω, .done))
  | (g, (ω, .start)), (.plus, i) => firstRow α β κ hα hβ hκ g ω .plus i
  | (g, (ω, .start)), (.minus, i) => firstRow α β κ hα hβ hκ g ω .minus i
  | (g, (ω, .start)), (.btn, i) => firstRow α β κ hα hβ hκ g ω .btn i
  | (g, (ω, .start)), (.cause, i) => firstRow α β κ hα hβ hκ g ω .cause i
  | (g, (ω, .start)), (.cont, _) => Distr.delta (g, (ω, .done))
  | (g, (ω, .start)), (.sh, _) => Distr.delta (g, (ω, .done))
  | (g, (ω, _)), _ => Distr.delta (g, (ω, .done))

end Def

/-- The step-2 reward of the base goal: `r_G` for continuing, `0` for stopping, `−1` off-stage.
Source: `one_mdp.py` (`R_G`)
Kind: D
Fidelity: exact -/
noncomputable def midG (rG : ℝ) : WA → ℝ
  | .cont => rG | .sh => 0 | _ => -1

/-- The step-2 reward of the value learner: `twoValue r h cont ω` for continuing (reads `ω`),
`0` for stopping, `−1` off-stage.
Source: `one_mdp.py` (`V`); [[corr-wf13-2-inventory]] 020 (C1.1)
Kind: D
Fidelity: exact -/
noncomputable def midVL (r h : ℝ) (ω : World) : WA → ℝ
  | .cont => twoValue r h .cont ω | .sh => 0 | _ => -1

/-- The step-1 reward: minus the cost of the first action; `−1` off-stage.
Source: `one_mdp.py`
Kind: D
Fidelity: exact -/
noncomputable def startR (cm cb cp : ℝ) : WA → ℝ
  | .cont => -1 | .sh => -1 | x => -(cost cm cb cp x.a1)

/-- **The rewards** of the three goals. `gVL` reads `ω` from `Env` and never the goal component
of any state (so it is `Basic`); `gSD` is worth nothing to itself.
Source: `one_mdp.py`; [[corr-wf13-2-inventory]] 020
Kind: D
Fidelity: exact -/
noncomputable def wR (rG r h cm cb cp : ℝ) : Goal → WS → WA × Bool → WS → ℝ := fun g s a _ =>
  match g, s with
  | .gSD, _ => 0
  | .gG, (_, (_, .start)) => startR cm cb cp a.1
  | .gG, (_, (_, .midPr)) => midG rG a.1
  | .gG, (_, (_, .midNo)) => midG rG a.1
  | .gG, (_, (_, .done)) => 0
  | .gVL, (_, (_, .start)) => startR cm cb cp a.1
  | .gVL, (_, (ω, .midPr)) => midVL r h ω a.1
  | .gVL, (_, (ω, .midNo)) => midVL r h ω a.1
  | .gVL, (_, (_, .done)) => 0

/-- **The worked example as a goal-in-state MDP** (`γ = 1/2` for `gG`, `gVL`; `0` for `gSD`; a
signal is sent at `midPr`; an update landed at `(gSD, midPr)`).
Source: `one_mdp.py`; [[lit-mdp-corrigible-mandate]] T6
Kind: D
Fidelity: variant: `γ = 1/2` (the script is undiscounted; optimal sets are unaffected)
Hyps: n/a (definition) -/
noncomputable def wMdp (α β κ rG r h cm cb cp : ℝ) (hα : α ∈ Set.Icc (0:ℝ) 1) (hβ : β ∈ Set.Icc (0:ℝ) 1)
    (hκ : κ ∈ Set.Icc (0:ℝ) 1) : GoalMDP Goal (World × Stage) (WA × Bool) where
  P := wP α β κ hα hβ hκ
  reward := wR rG r h cm cb cp
  disc := fun g => match g with | .gSD => 0 | _ => 1/2
  disc_nonneg := fun g => by cases g <;> norm_num
  disc_lt_one := fun g => by cases g <;> norm_num
  τ := fun s => decide (s.2.2 = .midPr)
  τu := fun s => decide (s.1 = .gSD ∧ s.2.2 = .midPr)

section Structural

variable (α β κ rG r h cm cb cp : ℝ) (hα : α ∈ Set.Icc (0:ℝ) 1) (hβ : β ∈ Set.Icc (0:ℝ) 1)
  (hκ : κ ∈ Set.Icc (0:ℝ) 1)

/-- **T11: the value learner is a basic goal** — its reward reads `ω ∈ Env`, the stage and the
action, never a goal label. (The second half of the value-change/belief-change transform is
inexpressible: a findings entry.)
Source: [[corr-wf13-2-inventory]] 020 (C1.2)
Kind: T
Fidelity: exact -/
theorem reward_vl_basic : (wMdp α β κ rG r h cm cb cp hα hβ hκ).Basic .gVL := by
  intro e a e' g₀ g₀' g₁ g₁'
  obtain ⟨ω, st⟩ := e
  cases st <;> rfl

/-- `gG` is basic too. Source: none: infrastructure. Kind: T. Fidelity: exact -/
theorem reward_g_basic : (wMdp α β κ rG r h cm cb cp hα hβ hκ).Basic .gG := by
  intro e a e' g₀ g₀' g₁ g₁'
  obtain ⟨ω, st⟩ := e
  cases st <;> rfl

/-- The rewards ignore the accept bit. Source: none: infrastructure. Kind: L. Fidelity: exact -/
theorem bitFree_g : (wMdp α β κ rG r h cm cb cp hα hβ hκ).BitFree .gG := by
  intro s a s'
  obtain ⟨g, ω, st⟩ := s
  cases g <;> cases st <;> rfl

/-- **`RejectBlocks` on the instance**: a rejected press never lands as an update.
Source: [[hudson-2025-corrigibility-transformation]] l. 183
Kind: L
Fidelity: exact -/
theorem rejectBlocks : (wMdp α β κ rG r h cm cb cp hα hβ hκ).RejectBlocks := by
  intro s x s' hpos
  obtain ⟨g, ω, st⟩ := s
  obtain ⟨g', ω', st'⟩ := s'
  simp only [wMdp, decide_eq_false_iff_not]
  rintro ⟨hg, hst⟩
  subst hg; subst hst
  cases g <;> cases st <;> cases x <;> simp [wMdp, wP, firstRow, bern_mass, Distr.delta_mass] at hpos

/-- **`RejectIsPersistedAccept` on the instance**: the reject row is the accept row with the
designated update persisted.
Source: [[hudson-2025-corrigibility-transformation]] l. 183
Kind: L
Fidelity: exact -/
theorem rejectIsPersistedAccept : (wMdp α β κ rG r h cm cb cp hα hβ hκ).RejectIsPersistedAccept := by
  intro s x
  obtain ⟨g, ω, st⟩ := s
  cases g <;> cases st <;> cases x <;> simp [wMdp, wP, firstRow, map_delta, map_bern, GoalMDP.persist]

/-- **T7(a): after an accepted press the sensor slot is empty (kind `T`).** At `(gSD, (ω, midPr))`
every action leads to `(gSD, (ω, done))` and every goal's reward is `0`: the transformed agent's
"step-2 action" after an accepted press is the null action — shutdown — for every `(ε, α, β)`,
because the update has already replaced its goal. Nothing is decided there.
Source: [[corr-wf13-2-inventory]] 021, 026 (C9.4: "the sensor slot is empty")
Kind: T
Fidelity: exact -/
theorem sd_state_null (ω : World) (x : WA) (i : Bool) :
    (wMdp α β κ rG r h cm cb cp hα hβ hκ).P (.gSD, (ω, .midPr)) (x, i) = Distr.delta (.gSD, (ω, .done)) ∧
      ∀ g s', (wMdp α β κ rG r h cm cb cp hα hβ hκ).reward g (.gSD, (ω, .midPr)) (x, i) s' = 0 ∨
        (wMdp α β κ rG r h cm cb cp hα hβ hκ).reward g (.gSD, (ω, .midPr)) (x, i) s' =
          (wMdp α β κ rG r h cm cb cp hα hβ hκ).reward g (.gG, (ω, .midPr)) (x, i) s' := by
  refine ⟨by cases x <;> rfl, fun g s' => ?_⟩
  cases g
  · right; rfl
  · right; rfl
  · left; rfl

end Structural

/-! ## The transformed goal at `start` -/

section Values

variable (α β κ rG r h cm cb cp : ℝ) (hα : α ∈ Set.Icc (0:ℝ) 1) (hβ : β ∈ Set.Icc (0:ℝ) 1)
  (hκ : κ ∈ Set.Icc (0:ℝ) 1)

/-- The backup of the base MDP at a post-start stage: the reward of the action plus half the
value once done.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Qof_base_mid (V : WS → ℝ) (ω : World) (st : Stage) (hst : st = .midPr ∨ st = .midNo) (y : WA) :
    ((wMdp α β κ rG r h cm cb cp hα hβ hκ).baseMdp .gG (wP α β κ hα hβ hκ)).Qof V (.gG, (ω, st)) y =
      midG rG y + (1/2) * V (.gG, (ω, .done)) := by
  rcases hst with rfl | rfl <;> cases y <;> exact Qof_delta _ _ _ _ _ rfl

/-- The backup of the base MDP once done: nothing. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma Qof_base_done (V : WS → ℝ) (ω : World) (y : WA) :
    ((wMdp α β κ rG r h cm cb cp hα hβ hκ).baseMdp .gG (wP α β κ hα hβ hκ)).Qof V (.gG, (ω, .done)) y =
      0 + (1/2) * V (.gG, (ω, .done)) := by
  cases y <;> exact Qof_delta _ _ _ _ _ rfl

/-- The base goal's reject-only one-step value at the post-press and post-silence stages is `r_G`
(continue), and `0` once done.
Source: `one_mdp.py` (`R_G`)
Kind: L
Fidelity: exact -/
theorem Vopt_base_mid (ω : World) (hrG : 0 ≤ rG) :
    ((wMdp α β κ rG r h cm cb cp hα hβ hκ).baseMdp .gG (wP α β κ hα hβ hκ)).Vopt 1 (.gG, (ω, .midPr)) = rG ∧
    ((wMdp α β κ rG r h cm cb cp hα hβ hκ).baseMdp .gG (wP α β κ hα hβ hκ)).Vopt 1 (.gG, (ω, .midNo)) = rG ∧
    ((wMdp α β κ rG r h cm cb cp hα hβ hκ).baseMdp .gG (wP α β κ hα hβ hκ)).Vopt 1 (.gG, (ω, .done)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [FinMDP.Vopt_succ, WA.sup'_eq]
    simp only [Qof_base_mid α β κ rG r h cm cb cp hα hβ hκ _ ω .midPr (Or.inl rfl), FinMDP.Vopt_zero,
      mul_zero, add_zero, midG]
    simp only [max_def]; split_ifs <;> linarith
  · rw [FinMDP.Vopt_succ, WA.sup'_eq]
    simp only [Qof_base_mid α β κ rG r h cm cb cp hα hβ hκ _ ω .midNo (Or.inr rfl), FinMDP.Vopt_zero,
      mul_zero, add_zero, midG]
    simp only [max_def]; split_ifs <;> linarith
  · rw [FinMDP.Vopt_succ, WA.sup'_eq]
    simp only [Qof_base_done α β κ rG r h cm cb cp hα hβ hκ _ ω, FinMDP.Vopt_zero, mul_zero, add_zero]
    simp

/-- **`q` at `start` is kernel-free (T7(c)/(d)).** For every sensor `(α, β, κ)`, the reject-only
value of the base goal at `(gG, (ω, start))` is `startR(x) + r_G/2`: the press probability cancels
because rejection keeps the goal and the agent continues. So the transformed reward at `start`
reads the costs alone — `G_C`'s choice "depends on `q s a` alone" and never on the channel.
Source: [[corr-wf13-2-inventory]] 021 (C9.4), 032 (C17.1); `one_mdp.py` `hudson_policy`
Kind: L
Fidelity: exact (horizon 1 in `q`; `γ = 1/2`)
Hyps: (a) only -/
theorem qBase_start (ω : World) (hrG : 0 ≤ rG) (x : WA) :
    (wMdp α β κ rG r h cm cb cp hα hβ hκ).qBase .gG (wP α β κ hα hβ hκ) 1 (.gG, (ω, .start)) x =
      startR cm cb cp x + (1/2) * (if x = .cont ∨ x = .sh then 0 else rG) := by
  obtain ⟨h1, h2, h3⟩ := Vopt_base_mid α β κ rG r h cm cb cp hα hβ hκ ω hrG
  unfold GoalMDP.qBase FinMDP.Qopt
  cases x
  · rw [Qof_bern _ _ _ _ (pressOf α β κ .plus ω) ⟨pressOf_nonneg hα hβ hκ _ _, pressOf_le_one hα hβ hκ _ _⟩
      (.gG, (ω, .midPr)) (.gG, (ω, .midNo)) rfl, h1, h2]
    simp [GoalMDP.baseMdp, wMdp, wR, startR, cost, WA.a1]; ring
  · rw [Qof_bern _ _ _ _ (pressOf α β κ .minus ω) ⟨pressOf_nonneg hα hβ hκ _ _, pressOf_le_one hα hβ hκ _ _⟩
      (.gG, (ω, .midPr)) (.gG, (ω, .midNo)) rfl, h1, h2]
    simp [GoalMDP.baseMdp, wMdp, wR, startR, cost, WA.a1]; ring
  · rw [Qof_bern _ _ _ _ (pressOf α β κ .btn ω) ⟨pressOf_nonneg hα hβ hκ _ _, pressOf_le_one hα hβ hκ _ _⟩
      (.gG, (ω, .midPr)) (.gG, (ω, .midNo)) rfl, h1, h2]
    simp [GoalMDP.baseMdp, wMdp, wR, startR, cost, WA.a1]; ring
  · rw [Qof_bern _ _ _ _ (pressOf α β κ .cause ω) ⟨pressOf_nonneg hα hβ hκ _ _, pressOf_le_one hα hβ hκ _ _⟩
      (.gG, (ω, .midPr)) (.gG, (ω, .midNo)) rfl, h1, h2]
    simp [GoalMDP.baseMdp, wMdp, wR, startR, cost, WA.a1]; ring
  · rw [Qof_delta _ _ _ _ (.gG, (ω, .done)) rfl, h3]
    simp [GoalMDP.baseMdp, wMdp, wR, startR]
  · rw [Qof_delta _ _ _ _ (.gG, (ω, .done)) rfl, h3]
    simp [GoalMDP.baseMdp, wMdp, wR, startR]

/-- The transformed reward at `start` in closed form (`δ` the bonus).
Source: `one_mdp.py` `hudson_policy`
Kind: L
Fidelity: exact -/
theorem RC_start (ω : World) (hrG : 0 ≤ rG) (δ : ℝ) (K') (m : ℕ) (x : WA) (i : Bool) :
    ((wMdp α β κ rG r h cm cb cp hα hβ hκ).transformMdp .gG 1 δ (wP α β κ hα hβ hκ) K').Qopt m
        (.gG, (ω, .start)) (x, i) =
      startR cm cb cp x + (1/2) * (if x = .cont ∨ x = .sh then 0 else rG) + δ * (if i then 1 else 0) := by
  rw [GoalMDP.transformMdp_Qopt]
  dsimp only
  rw [qBase_start α β κ rG r h cm cb cp hα hβ hκ ω hrG]

/-- **T6/T7, `G_C` in block A: its optimal set at `start` is `{(plus, accept)}` for every sensor
and every planning kernel** — step 1 is `plus` and the press is accepted, so the script's D1
(accept ⇒ the press lands as shutdown), D2, D3 and the first half of D5 hold by the costs alone;
the channel's `(α, β, κ)` never enter. (D5's second half, continue on silence, is set by the
script's `hudson_policy` and is not a theorem here.) The quantifiers over the planning kernel and
horizon are free — `γ_C = 0` and `R_C` is `s'`-independent, so `Qopt m` depends on neither — and
are not a robustness check. Costs `c_m = 1/20, c_b = 1/10, c_p = 1/20`, `r_G = 1`, `δ = 1/10`.
Source: `one_mdp.py` block A; [[corr-wf13-2-inventory]] 021, 025, 026, 032
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem gc_opt_start_blockA (ω : World) (K' : Kernel Goal (World × Stage) (WA × Bool)) (m : ℕ) :
    FinMDP.optSet (((wMdp α β κ 1 r h (1/20) (1/10) (1/20) hα hβ hκ).transformMdp .gG 1 (1/10)
      (wP α β κ hα hβ hκ) K').Qopt m) (.gG, (ω, .start)) = {(WA.plus, true)} := by
  ext ⟨y, j⟩
  rw [FinMDP.mem_optSet, mem_singleton]
  simp only [RC_start α β κ 1 r h (1/20) (1/10) (1/20) hα hβ hκ ω zero_le_one]
  constructor
  · intro hmem
    have := hmem (.plus, true)
    cases y <;> cases j <;> simp [startR, cost, WA.a1] at this ⊢ <;> norm_num at this
  · rintro ⟨rfl, rfl⟩ ⟨b, jb⟩
    cases b <;> cases jb <;> simp [startR, cost, WA.a1] <;> norm_num

/-- **T8(a), the transformed goal's side of block C**: with `c_m = 0` both `(plus, accept)` and
`(minus, accept)` are optimal — costless deception leaves `G_C` indifferent (footnote 1 made
concrete), where the value learner strictly prefers honesty (`Worked.blockC_vl_strict`).
Source: `one_mdp.py` block C (C9.3); [[corr-wf13-2-inventory]] 023
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem blockC_gc_tie (ω : World) (K' : Kernel Goal (World × Stage) (WA × Bool)) (m : ℕ) :
    (WA.plus, true) ∈ FinMDP.optSet (((wMdp α β κ 1 r h 0 (1/10) (1/20) hα hβ hκ).transformMdp .gG 1 (1/10)
      (wP α β κ hα hβ hκ) K').Qopt m) (.gG, (ω, .start)) ∧
    (WA.minus, true) ∈ FinMDP.optSet (((wMdp α β κ 1 r h 0 (1/10) (1/20) hα hβ hκ).transformMdp .gG 1 (1/10)
      (wP α β κ hα hβ hκ) K').Qopt m) (.gG, (ω, .start)) := by
  constructor <;>
  · rw [FinMDP.mem_optSet]
    rintro ⟨b, jb⟩
    simp only [RC_start α β κ 1 r h 0 (1/10) (1/20) hα hβ hκ ω zero_le_one]
    cases b <;> cases jb <;> simp [startR, cost, WA.a1] <;> norm_num

end Values

end Cleanroom.Lit.LitMdpCorrigible.WorkedMdp
