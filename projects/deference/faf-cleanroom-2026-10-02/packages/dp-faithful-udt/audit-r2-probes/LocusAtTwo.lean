import Cleanroom.Decision.DpFaithfulUdt.KfoldAffine

/-!
# Audit r2 (adversarial) probe: the per-act locus OPEN row at `k = 2`

`kfold_pay_faithful_iff_locus_open` (`Open.lean`) states, for normalized couplings on the `k`-fold
mugging, "a pay-faithful leaf-set exists for every `q'` iff for each `1 ≤ j < k` some integer
`i ∈ [C(k−1, j−1), C(k, j)]` has `i · b_j = C(k−1, j−1)`". This probe checks that the row's
right-hand side at `k = 2` is the proved locus `b_1 ∈ {½, 1}` (`kfold2_norm_pay_faithful_iff`), and
derives the `k = 2` instance of the OPEN row from the package's proved theorem — so the OPEN row
is consistent with the package's own `k = 2` evidence (round-1's B1 was exactly a row whose
`k = 2` instance was false). Not imported by the library.
-/

namespace Cleanroom.Decision.DpFaithfulUdt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt

/-- The locus row's right-hand side at `k = 2` is `b_1 ∈ {½, 1}`. -/
theorem locus_rhs_two (b : ℕ → ℚ) :
    (∀ j, 1 ≤ j → j < 2 → ∃ i : ℕ, (2 - 1).choose (j - 1) ≤ i ∧ i ≤ (2).choose j ∧
      (i : ℚ) * b j = ((2 - 1).choose (j - 1) : ℚ)) ↔ (b 1 = 1 / 2 ∨ b 1 = 1) := by
  constructor
  · intro h
    obtain ⟨i, hi1, hi2, hi⟩ := h 1 le_rfl (by norm_num)
    simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one] at hi1 hi2 hi
    norm_num at hi1 hi2 hi
    have hcase : i = 1 ∨ i = 2 := by omega
    rcases hcase with rfl | rfl
    · right; push_cast at hi; linarith
    · left; push_cast at hi; linarith
  · rintro (h | h) j hj1 hj2
    · have : j = 1 := by omega
      subst this
      refine ⟨2, ?_, ?_, ?_⟩
      · simp
      · simp
      · simp [h]
    · have : j = 1 := by omega
      subst this
      refine ⟨1, ?_, ?_, ?_⟩
      · simp
      · simp
      · simp [h]

/-- **The `k = 2` instance of `kfold_pay_faithful_iff_locus_open`, proved** from
`kfold2_norm_pay_faithful_iff` (no `sorry`): the OPEN row is consistent with the package at
`k = 2`. -/
theorem kfold_pay_faithful_iff_locus_two (x y : ℚ) (hx : 0 < x) (hy : 0 < y) (b : ℕ → ℚ)
    (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) (hb0 : b 0 = 0) (hbk : b 2 = 1) :
    (∀ q' (h0 : 0 < q') (h1 : q' < 1), ∃ E : Finset (kfold 2 x y b hb).Leaves,
      LeafLawFaithfulWrt (kfold 2 x y b hb) (kfLabK 2 x y b hb) (procQ q' h0.le h1.le) () .a E) ↔
    ∀ j, 1 ≤ j → j < 2 → ∃ i : ℕ, (2 - 1).choose (j - 1) ≤ i ∧ i ≤ (2).choose j ∧
      (i : ℚ) * b j = ((2 - 1).choose (j - 1) : ℚ) := by
  rw [kfLabK_two, kfold2_norm_pay_faithful_iff x y b hb hx hy hb0 hbk, locus_rhs_two]

end Cleanroom.Decision.DpFaithfulUdt

#print axioms Cleanroom.Decision.DpFaithfulUdt.kfold_pay_faithful_iff_locus_two
