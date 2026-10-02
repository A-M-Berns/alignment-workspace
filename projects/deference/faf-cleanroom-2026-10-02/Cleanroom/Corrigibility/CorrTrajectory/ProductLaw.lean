import Cleanroom.Corrigibility.CorrTrajectory.Process

/-!
# `corr-trajectory` — `ProductLaw`: independent rounds as a product of FAF `Distr`s

Infrastructure for the multi-round witnesses (T3's C7, T4's E1): the product `prod2 μ₁ μ₂` of two
finite laws, expectations of functions of one coordinate, and sums over the atoms "first coordinate
fixed" — the conditional independence the sources assume between rounds.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.CorrTrajectory

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- The product law on `A × B`. Source: none: infrastructure (independent rounds). Kind: D. Fidelity: n/a -/
noncomputable def prod2 (μ₁ : Distr A) (μ₂ : Distr B) : Distr (A × B) where
  mass ω := μ₁.mass ω.1 * μ₂.mass ω.2
  nonneg ω := mul_nonneg (μ₁.nonneg _) (μ₂.nonneg _)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, μ₂.sum_eq_one, mul_one]
    exact μ₁.sum_eq_one

/-- `prod2_mass` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma prod2_mass (μ₁ : Distr A) (μ₂ : Distr B) (ω : A × B) :
    (prod2 μ₁ μ₂).mass ω = μ₁.mass ω.1 * μ₂.mass ω.2 := rfl

/-- `E[g(ω₁)]` under the product is `E_{μ₁}[g]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_prod2_fst (μ₁ : Distr A) (μ₂ : Distr B) (g : A → ℝ) :
    expect (prod2 μ₁ μ₂) (fun ω => g ω.1) = expect μ₁ g := by
  unfold expect
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => ?_
  simp only [prod2_mass]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have : ∑ b, μ₂.mass b = 1 := μ₂.sum_eq_one
  rw [this]; ring

/-- `E[g(ω₂)]` under the product is `E_{μ₂}[g]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_prod2_snd (μ₁ : Distr A) (μ₂ : Distr B) (g : B → ℝ) :
    expect (prod2 μ₁ μ₂) (fun ω => g ω.2) = expect μ₂ g := by
  unfold expect
  rw [Fintype.sum_prod_type]
  simp only [prod2_mass]
  have : ∀ a, ∑ b, μ₁.mass a * μ₂.mass b * g b = μ₁.mass a * ∑ b, μ₂.mass b * g b := by
    intro a; rw [Finset.mul_sum]; refine sum_congr rfl fun b _ => by ring
  simp only [this, ← Finset.sum_mul, μ₁.sum_eq_one, one_mul]

/-- The sum over the atom "first coordinate `= a`" of a function of the second coordinate factorizes.
Source: none: infrastructure (conditional independence of rounds). Kind: L. Fidelity: n/a -/
lemma sum_filter_fst (μ₁ : Distr A) (μ₂ : Distr B) (a : A) (g : B → ℝ) :
    ∑ ω ∈ univ.filter (fun ω : A × B => ω.1 = a), (prod2 μ₁ μ₂).mass ω * g ω.2 =
      μ₁.mass a * ∑ b, μ₂.mass b * g b := by
  rw [sum_filter, Fintype.sum_prod_type]
  simp only [prod2_mass]
  rw [Finset.sum_eq_single a]
  · simp only [if_true]
    rw [Finset.mul_sum]; refine sum_congr rfl fun b _ => by ring
  · intro a' _ ha'; simp [ha']
  · intro h; exact absurd (mem_univ a) h

/-- The mass of the atom "first coordinate `= a`" is `μ₁(a)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_filter_fst_one (μ₁ : Distr A) (μ₂ : Distr B) (a : A) :
    ∑ ω ∈ univ.filter (fun ω : A × B => ω.1 = a), (prod2 μ₁ μ₂).mass ω = μ₁.mass a := by
  have := sum_filter_fst μ₁ μ₂ a (fun _ => 1)
  simp only [mul_one] at this
  rw [this, μ₂.sum_eq_one, mul_one]

end Cleanroom.Corrigibility.CorrTrajectory
