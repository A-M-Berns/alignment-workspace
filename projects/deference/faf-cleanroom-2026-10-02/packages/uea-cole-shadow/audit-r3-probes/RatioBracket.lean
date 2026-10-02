import Cleanroom.Uea.UeaColeShadow.Chain

/-!
Round-3 fidelity probe (uea-cole-shadow): what `Chain.dyadic_ratio_bracket` does and does not say about the
ledger's "`gap/bound` inside `(1/4, 1/2)` only from `m = 4`". The bracket's lower end `m/(4(m+2))` is below `1/4`
for every `m`, so the bracket alone never places the ratio above `1/4`; the `m = 4` value (`≈ 0.272 > 1/4`) follows
from `dyadic4_gap` and `dyadic4_bound` instead. Not imported by the library.
-/

namespace Cleanroom.Uea.UeaColeShadow.Chain

/-- The lower end of the bracket is below `1/4` for every `m`. -/
theorem probe_bracket_lower_lt_quarter (m : ℕ) : (m : ℝ) / (4 * (m + 2)) < 1 / 4 := by
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  rw [div_lt_iff₀ (by positivity)]
  linarith

/-- At `m = 4` the ratio is above `1/4` (`gap > bound/4`), from the two `m = 4` evaluation lemmas. -/
theorem probe_dyadic4_ratio_gt_quarter :
    (chain (dyadic 4 (by norm_num))).odds (chainPol (dyadic 4 (by norm_num))) 0 (goH 0) *
        (1 + ((chain (dyadic 4 (by norm_num))).T : ℝ)) / 4 <
      (chain (dyadic 4 (by norm_num))).gap (chainPol (dyadic 4 (by norm_num))) 0 (goH 0) := by
  rw [dyadic4_gap, dyadic4_bound]
  norm_num

end Cleanroom.Uea.UeaColeShadow.Chain

#print axioms Cleanroom.Uea.UeaColeShadow.Chain.probe_bracket_lower_lt_quarter
#print axioms Cleanroom.Uea.UeaColeShadow.Chain.probe_dyadic4_ratio_gt_quarter
