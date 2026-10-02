import Cleanroom.Udt.UdtHarmonyBargain

/-!
# udt-harmony-bargain — audit round 1, lens `adversarial`: probes

Not imported by the library. Each probe tests whether a headline could be true for a reason the
source did not intend, or whether a hypothesis the ledger calls load-bearing really is.

1. `stagHunt_HH_bargainNash`: in the Stag Hunt, `((H, ∅), (H, ∅))` is a **pure Nash equilibrium of
   the bargaining game** with the non-optimal outcome `(H,H)`, under every selector. So Proposition
   S(a) (`harmonious_subset_optimal`) is not true for the trivial reason "every Nash outcome is
   optimal": the trembling-hand hypothesis does the work.
2. `tn_ll_not_bargainNash`: on TN-V2 the prior-optimal outcome `(large, large)` is not even a
   **Nash** outcome of the updated bargaining game (for every singleton-faithful selector). The
   package proves only that `(both, both)` *is* harmonious there; this shows updating also
   *removes* the optimum, so "updating breaks harmony" holds in the strong sense.
3. `mug_refuse_bargainNash`: `((refuse, ∅), (refuse, ∅))` is a Nash equilibrium of the two-prior
   mugging under every selector, so `Mugging.veto` is not "no profile is Nash".
4. `FR12`: a common-payoff game with a safe batna for each player (`V(in, y) = −1`, else `0`) has
   two pure harmonious profiles with **distinct optimal outcomes** `(out, y)` and `(in, x)` under
   every singleton-faithful selector — including every welfare rule with `W` injective on the
   optima. This kernel-checks the findings file's F6 sentence "with a safe batna other optima can
   arise" (which the package asserts without Lean, T7(d) not started) and shows that the
   "no safe batna" hypothesis of `unique_without_safe_batna` / `outcome_eq_of_injOn` is
   load-bearing, not decorative.
-/

namespace Cleanroom.Udt.UdtHarmonyBargain.AuditR1Adv

open Finset SafeParetoImprovements StrategicGame
open Cleanroom.Udt.UdtHarmonyBargain
open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Catalogue

/-! ### Shared helper: a singleton acceptable set pins the outcome (singleton-faithful `sel`) -/

/-- If player `j` accepts exactly `{O₀}`, the outcome is `O₀` or the batna profile; if moreover
`O₀ j = bⱼ`, the outcome's `j`-coordinate is `bⱼ`. Only `sel {O₀} = O₀` is used. -/
theorem outcome_coord_of_singleton' {N : Type} [Fintype N] [DecidableEq N] {A : N → Type}
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]
    {sel : Finset (Outcome A) → Outcome A} (hsel : SingletonFaithful sel)
    (σ : ∀ i, Proposal A i) (j : N) {O₀ : Outcome A} (h : (σ j).2 = {O₀}) :
    outcome sel σ = O₀ ∨ outcome sel σ = batna σ := by
  rcases outcome_eq_sel_or_batna sel σ with ⟨hne, hout⟩ | ⟨-, hout⟩
  · left
    have hsub : inter σ ⊆ {O₀} := by
      intro O hO
      rw [mem_inter] at hO
      have := hO j
      rwa [h] at this
    have heq : inter σ = {O₀} := (Finset.subset_singleton_iff.mp hsub).resolve_left hne.ne_empty
    rw [hout, heq, hsel]
  · right; exact hout

/-- If some player's acceptable set is empty, the outcome is the batna profile. -/
theorem outcome_eq_batna_of_empty {N : Type} [Fintype N] [DecidableEq N] {A : N → Type}
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]
    (sel : Finset (Outcome A) → Outcome A) (σ : ∀ i, Proposal A i) (j : N) (h : (σ j).2 = ∅) :
    outcome sel σ = batna σ := by
  apply outcome_of_empty
  rw [Finset.not_nonempty_iff_eq_empty]
  ext O
  simp only [mem_inter, Finset.notMem_empty, iff_false]
  intro hO
  have := hO j
  rw [h] at this
  exact Finset.notMem_empty _ this

theorem exists_ne_fin_two (i : Fin 2) : ∃ j : Fin 2, j ≠ i := by
  fin_cases i
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩

/-! ### Probe 1: Stag Hunt — a non-optimal pure Nash of the bargaining game -/

/-- `((H, ∅), (H, ∅))` is a pure Nash equilibrium of the Stag Hunt bargaining game with outcome
`(H,H)`, for every selector. Proposition S(a)'s THPE hypothesis is therefore load-bearing. -/
theorem stagHunt_HH_bargainNash (sel : Finset (Outcome StagHunt.Act) → Outcome StagHunt.Act) :
    BargainNash (commonGame StagHunt.V) sel (fun _ => (false, ∅)) ∧
      outcome sel (fun _ => (false, ∅)) = StagHunt.HH := by
  set σ : ∀ i : Fin 2, Proposal StagHunt.Act i := fun _ => (false, ∅) with hσ
  have hbσ : batna σ = StagHunt.HH := by
    funext k; fin_cases k <;> rfl
  have hout : outcome sel σ = StagHunt.HH := by
    rw [outcome_eq_batna_of_empty sel σ 0 rfl, hbσ]
  refine ⟨?_, hout⟩
  intro i s'
  rw [commonGame_u, commonGame_u, hout, StagHunt.V_HH]
  obtain ⟨j, hj⟩ := exists_ne_fin_two i
  have hj' : (Function.update σ i s' j).2 = ∅ := by
    rw [Function.update_of_ne hj]
  rw [outcome_eq_batna_of_empty sel _ j hj']
  apply StagHunt.V_le_one_of_ne
  intro heq
  have h1 := congrFun heq j
  have h2 : StagHunt.SS j = true := by fin_cases j <;> rfl
  rw [h2] at h1
  simp only [batna, Function.update_of_ne hj, hσ] at h1
  exact Bool.false_ne_true h1

/-! ### Probe 2: TN-V2 — the optimum is not a Nash outcome of the updated game -/

/-- For every singleton-faithful selector, no proposal profile with outcome `(large, large)` is a
Nash equilibrium of the updated TN-V2 bargaining game: `d_F` grabs `5 > 4` with `(both, {bb})`. -/
theorem tn_ll_not_bargainNash (sel : Finset TnOut → TnOut) (hsel : SingletonFaithful sel)
    (σ : ∀ i : TnPt, Proposal (fun _ => Box) i) (h : outcome sel σ = tnO .large .large) :
    ¬ BargainNash tnUpd sel σ := by
  intro hn
  have hdev := hn .F (.both, {tnO .both .both})
  rw [h, tnUpd_u_F, tnUpd_u_F] at hdev
  set σ' := Function.update σ .F (.both, {tnO .both .both}) with hσ'
  have hF : outcome sel σ' .F = .both := by
    rcases outcome_coord_of_singleton' hsel σ' .F (O₀ := tnO .both .both) (by simp [hσ'])
      with hout | hout
    · rw [hout]; rfl
    · rw [hout]; simp [batna, hσ']
  rw [tnUF_of_both _ hF, tnU_values.1.1] at hdev
  norm_num at hdev

/-! ### Probe 3: the mugging — the refuse profile is Nash -/

theorem outcome_ne_pp_of_refuse_empty (sel : Finset MugOut → MugOut)
    (σ : ∀ i : Fin 2, Proposal (fun _ => Act2) i) (j : Fin 2) (hj : σ j = (.b, ∅)) :
    outcome sel σ ≠ pp := by
  rw [outcome_eq_batna_of_empty sel σ j (by rw [hj])]
  intro heq
  have := congrFun heq j
  simp [batna, pp, hj] at this

/-- `((refuse, ∅), (refuse, ∅))` is a Nash equilibrium of the two-prior mugging's bargaining game
under every selector (every outcome reachable by a unilateral deviation is worth `0` to both). -/
theorem mug_refuse_bargainNash (sel : Finset MugOut → MugOut) :
    BargainNash mugGame sel (fun _ => (.b, ∅)) := by
  set σ : ∀ i : Fin 2, Proposal (fun _ => Act2) i := fun _ => (.b, ∅) with hσ
  have h0 : outcome sel σ ≠ pp := outcome_ne_pp_of_refuse_empty sel σ 0 rfl
  have key : ∀ (i j : Fin 2), j ≠ i → ∀ s' : Proposal (fun _ => Act2) i,
      outcome sel (Function.update σ i s') ≠ pp :=
    fun i j hj s' => outcome_ne_pp_of_refuse_empty sel _ j (by rw [Function.update_of_ne hj])
  unfold BargainNash
  rw [Fin.forall_fin_two]
  refine ⟨fun s' => ?_, fun s' => ?_⟩
  · rw [(mugGame_values.2.2 _ (key 0 1 (by decide) s')).1, (mugGame_values.2.2 _ h0).1]
  · rw [(mugGame_values.2.2 _ (key 1 0 (by decide) s')).2, (mugGame_values.2.2 _ h0).2]

/-! ### Probe 4: safe batnas — two distinct harmonious optima (F6's unchecked sentence) -/

namespace FR12

/-- Row: `false` = out, `true` = in. Column: `false` = x, `true` = y. -/
abbrev Act : Fin 2 → Type := fun _ => Bool

def outY : Outcome Act := ![false, true]
def inX : Outcome Act := ![true, false]
def inY : Outcome Act := ![true, true]

/-- `V(in, y) = −1`, every other outcome `0`: row `out` and column `x` are safe batnas. -/
noncomputable def V (O : Outcome Act) : ℝ := if O = inY then -1 else 0

theorem V_le (O : Outcome Act) : V O ≤ 0 := by unfold V; split_ifs <;> norm_num

theorem V_of_ne {O : Outcome Act} (h : O ≠ inY) : V O = 0 := by unfold V; rw [if_neg h]

theorem outY_ne_inY : outY ≠ inY := by decide
theorem inX_ne_inY : inX ≠ inY := by decide
theorem outY_ne_inX : outY ≠ inX := by decide

theorem V_of_row_out {O : Outcome Act} (h : O 0 = false) : V O = 0 := by
  apply V_of_ne
  intro heq
  have := congrFun heq 0
  rw [h] at this
  exact Bool.false_ne_true this

theorem V_of_col_x {O : Outcome Act} (h : O 1 = false) : V O = 0 := by
  apply V_of_ne
  intro heq
  have := congrFun heq 1
  rw [h] at this
  exact Bool.false_ne_true this

theorem isOpt_of_ne {O : Outcome Act} (h : O ≠ inY) : IsOpt V O := by
  intro O'
  rw [V_of_ne h]
  exact V_le O'

/-- Row's `out` is a safe batna. -/
theorem safe_row : Safe V 0 false := fun O hO => isOpt_of_ne (fun h => by
  have := congrFun h 0; rw [hO] at this; exact Bool.false_ne_true this)

/-- Column's `x` is a safe batna. -/
theorem safe_col : Safe V 1 false := fun O hO => isOpt_of_ne (fun h => by
  have := congrFun h 1; rw [hO] at this; exact Bool.false_ne_true this)

/-- `σ₁ = ((out, {(out,y)}), (x, {(out,y)}))`. -/
def σ1 : ∀ i : Fin 2, Proposal Act i := fun _ => (false, {outY})

/-- `σ₂ = ((out, {(in,x)}), (x, {(in,x)}))`. -/
def σ2 : ∀ i : Fin 2, Proposal Act i := fun _ => (false, {inX})

/-- A player proposing batna `false` (safe) and a singleton acceptable set `{O₀}` with `O₀ ≠ inY`
realises value `0` against every opponent profile — the player's maximum. -/
theorem value_of_safe_singleton (sel : Finset (Outcome Act) → Outcome Act)
    (hsel : SingletonFaithful sel) (i : Fin 2) (O₀ : Outcome Act) (hO₀ : O₀ ≠ inY)
    (τ : ∀ j : Fin 2, Proposal Act j) :
    V (outcome sel (Function.update τ i (false, {O₀}))) = 0 := by
  rcases outcome_coord_of_singleton' hsel (Function.update τ i (false, {O₀})) i (O₀ := O₀)
      (by simp) with hout | hout
  · rw [hout]; exact V_of_ne hO₀
  · rw [hout]
    fin_cases i
    · exact V_of_row_out (by simp [batna])
    · exact V_of_col_x (by simp [batna])

theorem harmonious_of_safe_singleton (sel : Finset (Outcome Act) → Outcome Act)
    (hsel : SingletonFaithful sel) (O₀ : Outcome Act) (hO₀ : O₀ ≠ inY) :
    HarmoniousPure (commonGame V) sel (fun _ => (false, {O₀})) := by
  apply thpe_of_dominant
  intro i s τ
  rw [bargain_payoff, bargain_payoff, ofStrategicProfile_update, ofStrategicProfile_update,
    commonGame_u, commonGame_u]
  have := value_of_safe_singleton sel hsel i O₀ hO₀ ((bargain (commonGame V) sel).ofStrategicProfile τ)
  simp only [toStrat_apply] at this ⊢
  rw [this]
  exact V_le _

theorem outcome_of_safe_singleton (sel : Finset (Outcome Act) → Outcome Act)
    (hsel : SingletonFaithful sel) (O₀ : Outcome Act) :
    outcome sel (fun _ => (false, {O₀})) = O₀ := by
  have hne : (inter (fun _ : Fin 2 => ((false, {O₀}) : Proposal Act _))).Nonempty :=
    ⟨O₀, by rw [mem_inter]; intro i; exact mem_singleton_self _⟩
  rw [outcome_of_nonempty sel hne]
  have heq : inter (fun _ : Fin 2 => ((false, {O₀}) : Proposal Act _)) = {O₀} := by
    ext O; rw [mem_inter]; simp
  rw [heq, hsel]

/-- **Two harmonious profiles with distinct optimal outcomes**, under every singleton-faithful
selector (hence every welfare rule, whatever `W` does on the optima): `(out, y)` and `(in, x)` are
both optimal, both realised by pure trembling-hand equilibria. With safe batnas, uniqueness of the
harmonious outcome fails even for `W` injective on the optima. -/
theorem two_harmonious_optima (sel : Finset (Outcome Act) → Outcome Act)
    (hsel : SingletonFaithful sel) :
    HarmoniousPure (commonGame V) sel σ1 ∧ HarmoniousPure (commonGame V) sel σ2 ∧
      outcome sel σ1 = outY ∧ outcome sel σ2 = inX ∧ outY ≠ inX ∧
      IsOpt V outY ∧ IsOpt V inX ∧ Safe V 0 false ∧ Safe V 1 false :=
  ⟨harmonious_of_safe_singleton sel hsel outY outY_ne_inY,
   harmonious_of_safe_singleton sel hsel inX inX_ne_inY,
   outcome_of_safe_singleton sel hsel outY, outcome_of_safe_singleton sel hsel inX,
   outY_ne_inX, isOpt_of_ne outY_ne_inY, isOpt_of_ne inX_ne_inY, safe_row, safe_col⟩

/-- A welfare rule for `V` with `W` injective on the optima exists (so the failure of uniqueness is
not an artifact of ties): `W := V + 1/2·[O = outY]`, `sel := argmaxSel W`. -/
noncomputable def W (O : Outcome Act) : ℝ := V O + (if O = outY then 1/2 else 0)

theorem W_paretoConsistent : ParetoConsistent (commonGame V) W := by
  intro O O' h
  rw [paretoDom_commonGame_iff] at h
  -- `V O < V O'` forces `O = inY` and `O' ≠ inY`
  have hO : O = inY := by
    by_contra hne
    rw [V_of_ne hne] at h
    exact absurd h (not_lt.mpr (V_le O'))
  have hO' : O' ≠ inY := by
    intro heq; rw [heq, hO] at h; exact lt_irrefl _ h
  unfold W
  rw [hO, V_of_ne hO', if_neg (by decide : inY ≠ outY)]
  unfold V
  rw [if_pos rfl]
  split_ifs <;> norm_num

theorem isWelfareSel_W : IsWelfareSel (commonGame V) (argmaxSel W) W :=
  isWelfareSel_argmaxSel W_paretoConsistent

theorem W_outY_ne_W_inX : W outY ≠ W inX := by
  unfold W
  rw [V_of_ne outY_ne_inY, V_of_ne inX_ne_inY, if_pos rfl, if_neg outY_ne_inX.symm]
  norm_num

/-- Under the injective-on-optima welfare rule `(argmaxSel W, W)`, both `σ₁` and `σ₂` are harmonious
with distinct outcomes: the "no safe batna" hypothesis of `outcome_eq_of_injOn` is load-bearing. -/
theorem two_harmonious_optima_welfare :
    HarmoniousPure (commonGame V) (argmaxSel W) σ1 ∧ HarmoniousPure (commonGame V) (argmaxSel W) σ2 ∧
      outcome (argmaxSel W) σ1 ≠ outcome (argmaxSel W) σ2 ∧ IsWelfareSel (commonGame V) (argmaxSel W) W := by
  have hsel : SingletonFaithful (argmaxSel W) := isWelfareSel_W.singletonFaithful
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := two_harmonious_optima (argmaxSel W) hsel
  exact ⟨h1, h2, by rw [h3, h4]; exact h5, isWelfareSel_W⟩

end FR12

end Cleanroom.Udt.UdtHarmonyBargain.AuditR1Adv
