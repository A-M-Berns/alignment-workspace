import Cleanroom.Uea.UeaColeShadow.Chain

/-!
# `uea-cole-shadow` audit round 3 (adversarial lens): what `dyadic_ratio_bracket` does and does not say

`Chain.dyadic_ratio_bracket` (repair round 2) proves `gap/bound ∈ (m/(4(m+2)), m/(2(m+2)))` for the dyadic chain,
`m ≥ 2`. Its docstring and the ledger's `theoremC_depth` witness cell then say "**so** the ratio lies in `(1/4, 1/2)`
only from `m = 4` on". That does not follow: the bracket's lower end `m/(4(m+2))` is below `1/4` for every `m`
(`probe_bracket_lower_lt_quarter`), so the bracket never places the ratio above `1/4`; it shows `ratio < 1/2` for all
`m ≥ 2` and a lower bound tending to `1/4` from below. Membership in `(1/4, 1/2)` at `m = 4` is a separate numeric fact,
here machine-checked from the library's exact values (`probe_dyadic4_ratio_gt_quarter`: `0.2718 > 1/4`); for `m ≥ 5`
it is claimed on the round-2 auditor's decimals and is not in the Lean. The N+ grade of the chain witness does not
depend on this (it rests on `dyadic4_informative`). Not imported by the library.
-/

namespace Cleanroom.Uea.UeaColeShadow.Chain

/-- The bracket's lower end is below `1/4` for every `m`. -/
theorem probe_bracket_lower_lt_quarter (m : ℕ) : (m : ℝ) / (4 * (m + 2)) < 1 / 4 := by
  have h : (0:ℝ) < 4 * (m + 2) := by positivity
  rw [div_lt_iff₀ h]
  linarith

/-- At `m = 4` the ratio `gap/bound` exceeds `1/4` (`25845/237728 > 1/10`): a numeric fact from `dyadic4_gap` and
`dyadic4_bound`, not a consequence of the bracket. -/
theorem probe_dyadic4_ratio_gt_quarter :
    (chain (dyadic 4 (by norm_num))).odds (chainPol (dyadic 4 (by norm_num))) 0 (goH 0) *
        (1 + ((chain (dyadic 4 (by norm_num))).T : ℝ)) / 4 <
      (chain (dyadic 4 (by norm_num))).gap (chainPol (dyadic 4 (by norm_num))) 0 (goH 0) := by
  rw [dyadic4_bound, dyadic4_gap]
  norm_num

end Cleanroom.Uea.UeaColeShadow.Chain

#print axioms Cleanroom.Uea.UeaColeShadow.Chain.probe_dyadic4_ratio_gt_quarter
