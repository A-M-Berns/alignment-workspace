import Cleanroom.Decision.DpCalibration.MiniDevices

/-!
# Five-and-ten: Remark 3.12's tremble-consistency instance and Remark 3.9's retraction (T14)

On the one-point five-and-ten tree (`a → 5`, `b → 10`, `O = ⊤`; `Σ_{5/10}` = all state
assignments on it):

* `fiveTen_take10_trembleConsistent` — take-10 (`δ_b`) is tremble-consistent w.r.t. `T_EDT`:
  for every `ε ∈ (0, 1)` the `ε`-calibrated state has both acts subjectively possible with
  values `5` and `10`, and `supp δ_b = {b}` is the argmax.
* `fiveTen_take5_not_trembleConsistent` — take-5 (`δ_a`) is not: every `ε`-calibrated state
  (unique where `ν_ε(⊤) = 1 > 0`) puts `a` and `b` in `A^+` with values `5 < 10`, so the support
  condition excludes `a`.
* `fiveTen_take5_limitOC_tEdt` — **the retraction** (Remark 3.9): take-5 with the state certain
  of the `5`-world *is* limit-calibrated and `T_EDT`-approved vacuously — Definition 10 alone
  does not deliver the verdict; it is the sequence route (Remark 3.12) that does.
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

/-- `Σ_{5/10}`: every state assignment on `fiveTen`.
Source: [[decision-problems-v2]] §3.2 Remark 3.12 ("the five-and-ten stipulations (one point,
leaf payoffs `5` and `10`, states free)")
Kind: D -/
def sigmaFiveTen : AbstractProblem FiveTenW Unit (fun _ => Act2) ℚ := {I | I.B = fiveTen}

/-- A sum over the leaves of `fiveTen` as two terms. Source: none: infrastructure. Kind: L -/
theorem fiveTen_sum {M : Type} [AddCommMonoid M] (f : fiveTen.Leaves → M) :
    ∑ ℓ, f ℓ = f ⟨.a, ()⟩ + f ⟨.b, ()⟩ := by
  unfold fiveTen at f ⊢
  rw [sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf]

/-- `ν` on `fiveTen`. Source: none: infrastructure. Kind: L -/
theorem fiveTen_nu (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset FiveTenW) :
    nu C fiveTen X =
      (if Act2.a ∈ X then (C ()).w .a else 0) + (if Act2.b ∈ X then (C ()).w .b else 0) := by
  rw [nu_eq_sum, fiveTen_sum]
  simp [fiveTen, leafLaw_decision, world_decision]

/-- `𝔼[r · 1_X]` on `fiveTen`. Source: none: infrastructure. Kind: L -/
theorem fiveTen_paySum (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset FiveTenW) :
    paySum C fiveTen X =
      (if Act2.a ∈ X then (C ()).w .a * 5 else 0) + (if Act2.b ∈ X then (C ()).w .b * 10 else 0) := by
  rw [paySum_eq_sum_ite, fiveTen_sum]
  simp [fiveTen, leafLaw_decision, world_decision, payoff_decision]

/-- `queried fiveTen = {()}`. Source: none: infrastructure. Kind: L -/
theorem fiveTen_queried : queried fiveTen = {()} := by
  unfold fiveTen; ext u; cases u; simp [queried_decision]

/-- The strict state of `procQ r` on `fiveTen` (`O = ⊤`).
Source: [[decision-problems-v2]] Remark 3.12 ("every `ε`-calibrated state")
Kind: D -/
noncomputable def ftState (r : ℚ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : State FiveTenW ℚ :=
  calibratedState (procQ r h0 h1) fiveTen Finset.univ (nu_univ_pos _ _)

/-- Beliefs of the strict state: `P(a) = r`, `P(b) = 1 − r`. Source: none: infrastructure. Kind: L -/
theorem ftState_pr (r : ℚ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    (ftState r h0 h1).pr (ftActEv () .a) = r ∧ (ftState r h0 h1).pr (ftActEv () .b) = 1 - r := by
  constructor <;> rw [ftState, calibratedState_pr, Finset.inter_univ, nu_univ, div_one, fiveTen_nu] <;>
    simp [ftActEv, procQ]

/-- Values of the strict state for interior `r`: `V(a) = 5`, `V(b) = 10`.
Source: [[decision-problems-v2]] Remark 3.12 ("both actions subjectively possible with values
`5` and `10`")
Kind: L -/
theorem ftState_V (r : ℚ) (h0 : 0 < r) (h1 : r < 1) :
    (ftState r h0.le h1.le).V (ftActEv () .a) = 5 ∧ (ftState r h0.le h1.le).V (ftActEv () .b) = 10 := by
  simp only [ftState, calibratedState_V, Finset.inter_univ, fiveTen_nu, fiveTen_paySum, ftActEv,
    procQ, FinDistr.act2_a, FinDistr.act2_b]
  have : (1 - r) ≠ 0 := by linarith
  constructor <;> simp <;> field_simp

/-- **Take-10 is tremble-consistent with respect to `T_EDT`** on `Σ_{5/10}` (Remark 3.12).
Source: [[decision-problems-v2]] §3.2 Remark 3.12 ("take-10 is tremble-consistent with respect
to `T_EDT`")
Kind: N+
Fidelity: exact -/
theorem fiveTen_take10_trembleConsistent :
    TrembleConsistent ftObs sigmaFiveTen (procQ 0 le_rfl zero_le_one)
      (fun C I => TEdt I.s ftActEv C I.B) := by
  refine ⟨1, one_pos, fun ε h0 h1 hlt => ?_⟩
  rw [tremble_procQ]
  obtain ⟨hi0, hi1⟩ := qeps_interior 0 ε le_rfl zero_le_one h0 hlt
  have hr0 := (qeps_mem 0 ε le_rfl zero_le_one h0.le h1).1
  have hr1 := (qeps_mem 0 ε le_rfl zero_le_one h0.le h1).2
  refine ⟨⟨fiveTen, fun _ => ftState ((1 - ε) * 0 + ε / 2) hr0 hr1⟩, rfl, ?_, ?_⟩
  · intro d _
    cases d
    exact strictOCAt_calibratedState ftObs _ fiveTen _ () _ rfl
  · intro d _ _ a ha
    cases d
    obtain ⟨hpa, hpb⟩ := ftState_pr ((1 - ε) * 0 + ε / 2) hr0 hr1
    obtain ⟨hva, hvb⟩ := ftState_V ((1 - ε) * 0 + ε / 2) hi0 hi1
    have hA : APlus (fun _ => ftState ((1 - ε) * 0 + ε / 2) hr0 hr1) ftActEv () = Finset.univ := by
      ext b
      simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      cases b
      · rw [hpa]; linarith
      · rw [hpb]; linarith
    rw [mem_argmaxPlus, hA]
    cases a
    · simp [procQ] at ha
    · refine ⟨Finset.mem_univ _, fun b _ => ?_⟩
      cases b <;> simp only [hva, hvb] <;> norm_num

/-- **Take-5 is not tremble-consistent with respect to `T_EDT`** on `Σ_{5/10}`: every
`ε`-calibrated state has both acts in `A^+` with values `5` and `10`, and the support condition
then excludes `a`.
Source: [[decision-problems-v2]] §3.2 Remark 3.12 ("take-5 is not, since every `ε`-calibrated
state makes both actions subjectively possible with values `5` and `10`")
Kind: N+
Fidelity: exact -/
theorem fiveTen_take5_not_trembleConsistent :
    ¬ TrembleConsistent ftObs sigmaFiveTen (procQ 1 zero_le_one le_rfl)
      (fun C I => TEdt I.s ftActEv C I.B) := by
  rintro ⟨ε₀, hε₀, h⟩
  have hmin0 : 0 < min ε₀ 1 := lt_min hε₀ one_pos
  have hmin1 : min ε₀ 1 ≤ 1 := min_le_right _ _
  have hmin2 : min ε₀ 1 ≤ ε₀ := min_le_left _ _
  set ε : ℚ := min ε₀ 1 / 2 with hε
  have h0 : 0 < ε := by rw [hε]; linarith
  have h1 : ε < 1 := by rw [hε]; linarith
  obtain ⟨I, hI, hstrict, hedt⟩ := h ε h0 h1.le (by rw [hε]; linarith)
  obtain ⟨B, s⟩ := I
  simp only [sigmaFiveTen, Set.mem_setOf_eq] at hI
  subst hI
  simp only at hstrict hedt
  rw [tremble_procQ] at hstrict
  obtain ⟨hi0, hi1⟩ := qeps_interior 1 ε zero_le_one le_rfl h0 h1
  have hr0 := (qeps_mem 1 ε zero_le_one le_rfl h0.le h1.le).1
  have hr1 := (qeps_mem 1 ε zero_le_one le_rfl h0.le h1.le).2
  -- the strict state is pinned modulo junk by uniqueness
  have hpos : 0 < nu (procQ ((1 - ε) * 1 + ε / 2) hr0 hr1) fiveTen (ftObs ()) :=
    nu_univ_pos (procQ ((1 - ε) * 1 + ε / 2) hr0 hr1) fiveTen
  have hs := hstrict () (by rw [fiveTen_queried]; simp) hpos
  have hs' := strictClausesAt_calibratedState ftObs (procQ ((1 - ε) * 1 + ε / 2) hr0 hr1) fiveTen
    (fun _ => ftState ((1 - ε) * 1 + ε / 2) hr0 hr1) () hpos rfl
  have hag := strictClausesAt_unique ftObs _ fiveTen s _ () hpos hs hs'
  obtain ⟨hpa, hpb⟩ := ftState_pr ((1 - ε) * 1 + ε / 2) hr0 hr1
  obtain ⟨hva, hvb⟩ := ftState_V ((1 - ε) * 1 + ε / 2) hi0 hi1
  have hP : ∀ X, (s ()).pr X = (ftState ((1 - ε) * 1 + ε / 2) hr0 hr1).pr X := by
    intro X; simp only [State.pr, hag.1]
  have hVa' : (s ()).V (ftActEv () .a) = 5 := by
    rw [hag.2 _ (by rw [hP, hpa]; exact hi0), hva]
  have hVb' : (s ()).V (ftActEv () .b) = 10 := by
    rw [hag.2 _ (by rw [hP, hpb]; linarith), hvb]
  -- `T_EDT` at `d` for `δ_a` needs `V(b) ≤ V(a)`
  have hA : APlus s ftActEv () = Finset.univ := by
    ext b
    simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    cases b
    · rw [hP, hpa]; linarith
    · rw [hP, hpb]; linarith
  have := hedt () (by rw [fiveTen_queried]; simp) ⟨.a, by rw [hA]; simp⟩ .a (by simp [procQ])
  rw [mem_argmaxPlus, hA] at this
  have hle := this.2 .b (Finset.mem_univ _)
  rw [hVa', hVb'] at hle
  norm_num at hle

/-- **The retraction (Remark 3.9)**: take-5 with the state certain of the `5`-world (`V ≡ 5`)
is limit-calibrated (the limit conditional under `δ_a^ε` *is* the `5`-world) and
`T_EDT`-approved vacuously (`A^+ = {a}`). Definition 10 alone does not deliver the five-and-ten
verdict.
Source: [[decision-problems-v2]] §3.1 Remark 3.9 ("the take-5 pair is limit-calibrated — the
limit conditional *is* the 5-world — and no state-honesty condition can forbid what is a fact
about the procedure"); dp-core-2-053
Kind: N+
Fidelity: exact -/
theorem fiveTen_take5_limitOC_tEdt :
    LimitOC (fun _ => State.dirac Act2.a 5) ftObs (procQ 1 zero_le_one le_rfl) fiveTen ∧
    TEdt (fun _ => State.dirac Act2.a 5) ftActEv (procQ 1 zero_le_one le_rfl) fiveTen := by
  obtain ⟨hta, htb⟩ := trembleW_procQ 1 zero_le_one le_rfl
  -- the polynomials on `fiveTen`
  have hnu : ∀ X : Finset FiveTenW, nuPoly (procQ 1 zero_le_one le_rfl) fiveTen X =
      (if Act2.a ∈ X then trembleW (procQ 1 zero_le_one le_rfl) () .a else 0) +
      (if Act2.b ∈ X then trembleW (procQ 1 zero_le_one le_rfl) () .b else 0) := by
    intro X
    rw [nuPoly_eq_sum, fiveTen_sum]
    simp [fiveTen, leafLawPoly, world_decision]
  have hpay : ∀ X : Finset FiveTenW, payPoly (procQ 1 zero_le_one le_rfl) fiveTen X =
      (if Act2.a ∈ X then trembleW (procQ 1 zero_le_one le_rfl) () .a * Polynomial.C 5 else 0) +
      (if Act2.b ∈ X then trembleW (procQ 1 zero_le_one le_rfl) () .b * Polynomial.C 10 else 0) := by
    intro X
    rw [payPoly_eq_sum, fiveTen_sum]
    simp [fiveTen, leafLawPoly, world_decision, payoff_decision]
  -- constant coefficients
  have hc0 : ∀ X : Finset FiveTenW,
      (nuPoly (procQ 1 zero_le_one le_rfl) fiveTen X).coeff 0 = if Act2.a ∈ X then 1 else 0 := by
    intro X
    rw [hnu, Polynomial.coeff_add, hta, htb]
    split_ifs <;> simp [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X]
  have hp0 : ∀ X : Finset FiveTenW,
      (payPoly (procQ 1 zero_le_one le_rfl) fiveTen X).coeff 0 = if Act2.a ∈ X then 5 else 0 := by
    intro X
    rw [hpay, Polynomial.coeff_add, hta, htb]
    split_ifs <;> simp [Polynomial.mul_coeff_zero, Polynomial.coeff_add, Polynomial.coeff_C,
      Polynomial.coeff_C_mul_X]
  have hdeg0 : ∀ X : Finset FiveTenW, Act2.a ∈ X →
      (nuPoly (procQ 1 zero_le_one le_rfl) fiveTen X).natTrailingDegree = 0 := by
    intro X hX
    exact natTrailingDegree_eq_of_coeff _ 0 (fun j hj => absurd hj (Nat.not_lt_zero j))
      (by rw [hc0, if_pos hX]; exact one_ne_zero)
  constructor
  · intro d _ _
    cases d
    have hObs : Act2.a ∈ ftObs () := by simp [ftObs]
    refine ⟨fun X => ?_, fun X hX => ?_⟩
    · rw [limitCond, hdeg0 _ hObs, hc0, hc0, State.dirac_pr]
      simp [ftObs]
    · rw [limitCond, hdeg0 _ hObs, hc0, hc0] at hX
      simp [ftObs] at hX
      have hmem : Act2.a ∈ X := by by_contra hc; simp [hc] at hX
      rw [ftObs, Finset.inter_univ, hdeg0 X hmem, hc0, hp0, if_pos hmem, if_pos hmem,
        State.dirac_V]
      norm_num
  · intro d _ _ a ha
    cases d
    have hA : APlus (fun _ => State.dirac Act2.a (5 : ℚ)) ftActEv () = {.a} := by
      ext b; cases b <;> simp [APlus, State.dirac, State.ofConst, FinDistr.pure_w, ftActEv]
    cases a
    · rw [mem_argmaxPlus, hA]
      exact ⟨Finset.mem_singleton_self _, fun b hb => by rw [Finset.mem_singleton] at hb; rw [hb]⟩
    · simp [procQ] at ha

end Cleanroom.Decision.DpCalibration
