import Cleanroom.Corrigibility.CorrScimCid.Scim
import Cleanroom.Corrigibility.CorrScimCid.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Helpers for the finite witness models

Bernoulli and point-mass noise on FAF's `Distr`, and the one lemma that turns an expectation over
the exogenous product space `Pt E` into a sum over a convenient finite type through an
equivalence (the witness models have `Unit` noise at every deterministic node, so `Pt E` is
`Bool`, or `Bool × (Bool × Bool × Bool)`, up to equivalence).

Source: none: infrastructure.
-/

namespace Cleanroom.Corrigibility.CorrScimCid

open FactoredSpaces Cleanroom.Found.CorrThreeStep

/-- Bernoulli noise: `P(true) = p`, `P(false) = 1 − p`.
Source: none: infrastructure
Kind: D -/
noncomputable def bern (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : Distr Bool where
  mass b := if b then p else 1 - p
  nonneg b := by cases b <;> simp <;> linarith
  sum_eq_one := by simp

@[simp] lemma bern_mass_true (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : (bern p h0 h1).mass true = p := rfl
@[simp] lemma bern_mass_false (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    (bern p h0 h1).mass false = 1 - p := rfl

/-- The trivial noise on `Unit`.
Source: none: infrastructure
Kind: D -/
noncomputable def unitD : Distr Unit := Distr.delta ()

@[simp] lemma unitD_mass (u : Unit) : unitD.mass u = 1 := by
  simp [unitD, Distr.delta_mass]

/-- An expectation over `Ω` is a sum over any equivalent type.
Source: none: infrastructure
Kind: L -/
lemma expect_equiv {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (μ : Distr Ω) (F : Ω → ℝ)
    (e : Ω ≃ Ω') : expect μ F = ∑ y, μ.mass (e.symm y) * F (e.symm y) := by
  unfold expect
  exact Fintype.sum_equiv e _ _ fun x => by simp

/-- A probability over `Ω` is a sum over any equivalent type.
Source: none: infrastructure
Kind: L -/
lemma prob_equiv {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (μ : Distr Ω) (A : Set Ω)
    [DecidablePred (· ∈ A)] (e : Ω ≃ Ω') :
    μ.prob A = ∑ y, if e.symm y ∈ A then μ.mass (e.symm y) else 0 := by
  unfold Distr.prob
  refine Fintype.sum_equiv e _ _ fun x => ?_
  simp [Set.indicator_apply]

/-- A restricted expectation over `Ω` is a sum over any equivalent type.
Source: none: infrastructure
Kind: L -/
lemma expectOn_equiv {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (μ : Distr Ω) (A : Set Ω)
    [DecidablePred (· ∈ A)] (X : Ω → ℝ) (e : Ω ≃ Ω') :
    expectOn μ A X = ∑ y, if e.symm y ∈ A then μ.mass (e.symm y) * X (e.symm y) else 0 := by
  rw [expectOn_apply]
  exact Fintype.sum_equiv e _ _ fun x => by simp

/-- The conditional expectation of a constant on a positive-probability set is that constant.
Source: none: infrastructure
Kind: L -/
lemma condExpect_const {Ω : Type*} [Fintype Ω] (μ : Distr Ω) {A : Set Ω} (hA : 0 < μ.prob A)
    (k : ℝ) : condExpect μ A (fun _ => k) = k := by
  rw [condExpect, expectOn_const, mul_div_cancel_right₀ _ hA.ne']

/-- The conditional expectation of a variable constant on the support of `A`.
Source: none: infrastructure
Kind: L -/
lemma condExpect_eq_const {Ω : Type*} [Fintype Ω] (μ : Distr Ω) {A : Set Ω} (hA : 0 < μ.prob A)
    {X : Ω → ℝ} {k : ℝ} (h : ∀ ω ∈ A, 0 < μ.mass ω → X ω = k) : condExpect μ A X = k := by
  rw [condExpect_congr μ h, condExpect_const μ hA]

end Cleanroom.Corrigibility.CorrScimCid
