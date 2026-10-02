import Cleanroom.Corrigibility.CorrGeneralObject.Bridge

/-!
# corr-general-object — T1: a modification raising a null event fails reflection everywhere

If `P ω₀ = 0 < Q ω₀` then the push toward `Q` is endorsed under no kernel of positive mass
(`not_endorsed_of_null`), and for *every* legitimacy event `L` of positive push mass both the
function form (`not_funLegit_of_null`) and the value form on the indicator of `ω₀`
(`not_valueLegit_ind_of_null`) fail. Corollary (D3's point): a modification with `¬ AbsCont Q P`
is legitimate under no kernel and no legitimacy event (`not_legit_of_not_absCont`). The
frame-level twin is `corr-reflect-frames`' `reflects_null_of_null` (radical I2.2).

Witness: two-point `P = (1, 0)`, `Q = (1/2, 1/2)`, `k = (1, 1)` (`w1_*`).

Source: [[general-object-final]] D3 remark, P1; [[corr-wf14b-inventory]] 002.
-/

namespace Cleanroom.Corrigibility.CorrGeneralObject

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- **A null event raised by the target is endorsed under no kernel of positive mass**: if
`P ω₀ = 0 < Q ω₀` and `0 < P(E_Q)` then `¬ Endorsed P k Q`.
Source: [[general-object-final]] P1 (`P_t(A | E_Q) ≤ P_t(A)/P_t(E_Q) = 0 ≠ Q(A)`); radical I2.2
Kind: P
Fidelity: exact (finite; the event `A` is a point — every finite null event contains a
`Q`-positive point when `Q(A) > 0`)
Hyps: (a) `0 < pushMass P k` is the guard (the conclusion is vacuous without it) -/
theorem not_endorsed_of_null (P : Distr Ω) {k : Ω → ℝ} (h : 0 < pushMass P k) {Q : Distr Ω}
    {ω₀ : Ω} (hP : P.mass ω₀ = 0) (hQ : 0 < Q.mass ω₀) : ¬ Endorsed P k Q := by
  intro hE
  have := hE ω₀
  rw [hP, zero_mul] at this
  have : 0 < pushMass P k * Q.mass ω₀ := mul_pos h hQ
  linarith

/-- **… and fails function-form legitimacy conditional on every `L` of positive push mass.**
Source: [[general-object-final]] P1 ("the same bound with `E_Q ∩ L_Q` in place of `E_Q`")
Kind: P
Fidelity: exact
Hyps: (a) `0 < P(E_Q ∧ L)` is the guard, quantified inside the conclusion -/
theorem not_funLegit_of_null (P : Distr Ω) (k : Ω → ℝ) {Q : Distr Ω} {ω₀ : Ω}
    (hP : P.mass ω₀ = 0) (hQ : 0 < Q.mass ω₀) :
    ∀ L : Finset Ω, 0 < ∑ ω ∈ L, P.mass ω * k ω → ¬ FunLegit P k Q L := by
  intro L hL hF
  have := hF ω₀
  rw [hP, zero_mul, ite_self] at this
  have : 0 < (∑ ω ∈ L, P.mass ω * k ω) * Q.mass ω₀ := mul_pos hL hQ
  linarith

/-- **… and fails value-form legitimacy on the indicator of the raised point, conditional on
every `L` of positive push mass**: `0 ≠ P(E_Q ∧ L) · Q ω₀`.
Source: [[general-object-final]] P1
Kind: P
Fidelity: exact
Hyps: (a) the guard, quantified inside the conclusion -/
theorem not_valueLegit_ind_of_null (P : Distr Ω) (k : Ω → ℝ) {Q : Distr Ω} {ω₀ : Ω}
    (hP : P.mass ω₀ = 0) (hQ : 0 < Q.mass ω₀) :
    ∀ L : Finset Ω, 0 < ∑ ω ∈ L, P.mass ω * k ω → ¬ ValueLegit P k Q L (ind {ω₀}) := by
  intro L hL hV
  unfold ValueLegit at hV
  have hlhs : ∑ ω ∈ L, P.mass ω * k ω * ind {ω₀} ω = 0 := by
    apply sum_eq_zero
    intro ω _
    unfold ind Cleanroom.Found.LitDdbFrames.ind
    by_cases hω : ω = ω₀
    · subst hω; rw [hP]; ring
    · simp [hω]
  have hrhs : expect Q (ind {ω₀}) = Q.mass ω₀ := by
    unfold expect ind Cleanroom.Found.LitDdbFrames.ind
    simp
  rw [hlhs, hrhs] at hV
  have : 0 < (∑ ω ∈ L, P.mass ω * k ω) * Q.mass ω₀ := mul_pos hL hQ
  linarith

/-- **D3's point**: a modification with `¬ AbsCont Q P` is endorsed under no kernel of positive
mass and function-form legitimate under no kernel and no legitimacy event of positive push mass.
Source: [[general-object-final]] D3 remark ("the excluded modifications can be legitimate under
no kernel")
Kind: C
Fidelity: exact
Hyps: (a) none beyond the positivity guards inside the conclusion -/
theorem not_legit_of_not_absCont (P Q : Distr Ω) (hQP : ¬ AbsCont Q P) :
    (∀ k : Ω → ℝ, 0 < pushMass P k → ¬ Endorsed P k Q) ∧
      ∀ (k : Ω → ℝ) (L : Finset Ω), 0 < ∑ ω ∈ L, P.mass ω * k ω → ¬ FunLegit P k Q L := by
  unfold AbsCont at hQP
  push Not at hQP
  obtain ⟨ω₀, hP, hQne⟩ := hQP
  have hQ : 0 < Q.mass ω₀ := lt_of_le_of_ne (Q.nonneg ω₀) (Ne.symm hQne)
  exact ⟨fun k hk => not_endorsed_of_null P hk hP hQ, fun k L hL => not_funLegit_of_null P k hP hQ L hL⟩

/-! ## Witness: the two-point instance -/

/-- `P = (1, 0)` on `Fin 2`. Source: mandate T1 witness. Kind: D. Fidelity: exact -/
def w1P : Distr (Fin 2) where
  mass := ![1, 0]
  nonneg i := by fin_cases i <;> norm_num
  sum_eq_one := by simp [Fin.sum_univ_two]

/-- `Q = (1/2, 1/2)` on `Fin 2`. Source: mandate T1 witness. Kind: D. Fidelity: exact -/
def w1Q : Distr (Fin 2) where
  mass := ![1/2, 1/2]
  nonneg i := by fin_cases i <;> norm_num
  sum_eq_one := by simp [Fin.sum_univ_two]; norm_num

/-- **N+ for T1**: with `P = (1, 0)`, `Q = (1/2, 1/2)`, the certain kernel `k ≡ 1` has push mass
`1 > 0` and the push is not endorsed; no `L` of positive push mass makes it function-form
legitimate.
Source: mandate T1 witness
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem w1_not_endorsed :
    0 < pushMass w1P (fun _ => (1 : ℝ)) ∧ ¬ Endorsed w1P (fun _ => (1 : ℝ)) w1Q ∧
      ∀ L : Finset (Fin 2), 0 < ∑ ω ∈ L, w1P.mass ω * 1 → ¬ FunLegit w1P (fun _ => 1) w1Q L := by
  have hm : pushMass w1P (fun _ => (1 : ℝ)) = 1 := by
    simp [pushMass, w1P, Fin.sum_univ_two]
  refine ⟨by rw [hm]; norm_num, ?_, ?_⟩
  · exact not_endorsed_of_null w1P (by rw [hm]; norm_num) (ω₀ := 1) (by simp [w1P]) (by simp [w1Q])
  · exact not_funLegit_of_null w1P _ (ω₀ := 1) (by simp [w1P]) (by simp [w1Q])

/-- The two-point instance is not absolutely continuous (so `not_legit_of_not_absCont` applies to
it). Source: mandate T1 witness. Kind: N+. Fidelity: exact -/
theorem w1_not_absCont : ¬ AbsCont w1Q w1P := by
  intro h
  have := h 1 (by simp [w1P])
  simp [w1Q] at this

end

end Cleanroom.Corrigibility.CorrGeneralObject
