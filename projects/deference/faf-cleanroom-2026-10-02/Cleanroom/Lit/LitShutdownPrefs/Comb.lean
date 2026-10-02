import Cleanroom.Lit.LitShutdownPrefs.Lottery

/-!
# Finite convex combinations of lotteries

`comb w hw0 hw1 Xs = ∑ i, w i • Xs i` over a `Fintype` index, with `expect_comb`. Used for the
ILPACS decompositions (`X = p₁X₁ + … + pₙXₙ`) and for prospects (`∑ s, μ s • dirac (F s)`).
-/

namespace Cleanroom.Lit.LitShutdownPrefs

namespace Lottery

open Finset

variable {T ι : Type} [Fintype ι]

/-- The convex combination `∑ i, w i • Xs i` of lotteries, for weights `w` in the simplex.
Source: Thornley 2025 §6 ("`p₁X₁ + p₂X₂ + ⋯ + pₙXₙ` denote a lottery which results in lottery `X₁` with probability `p₁`, …")
Kind: D
Fidelity: exact -/
noncomputable def comb (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (Xs : ι → Lottery T) : Lottery T where
  p := ∑ i, w i • (Xs i).p
  nonneg := fun t => by
    rw [Finsupp.finsetSum_apply]
    exact sum_nonneg fun i _ => by
      rw [Finsupp.smul_apply, smul_eq_mul]
      exact mul_nonneg (hw0 i) ((Xs i).nonneg t)
  sum_one := by
    rw [← wsum_one, wsum_finset_sum]
    simp_rw [wsum_smul, wsum_one]
    simp [(Xs _).sum_one, hw1]

/-- The mass function of a combination.
Source: none: infrastructure
Kind: L -/
theorem comb_p (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (Xs : ι → Lottery T) :
    (comb w hw0 hw1 Xs).p = ∑ i, w i • (Xs i).p := rfl

/-- `E_{∑ wᵢ Xᵢ}[g] = ∑ wᵢ E_{Xᵢ}[g]`.
Source: none: infrastructure
Kind: L -/
@[simp] theorem expect_comb (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (Xs : ι → Lottery T) (g : T → ℝ) :
    (comb w hw0 hw1 Xs).expect g = ∑ i, w i * (Xs i).expect g := by
  simp only [expect, comb, wsum_finset_sum, wsum_smul]

end Lottery

end Cleanroom.Lit.LitShutdownPrefs
