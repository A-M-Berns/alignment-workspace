import Cleanroom.Corrigibility.CorrPositionFinds.PrivateInfo

/-!
# Audit r3 (adversarial) probe — under the rule, the *weakest* static "`α` rises past the overseers" is trivially true

F-12's headline says the static "`α` rises as the agent exceeds the overseers" is "refuted in
both directions", and the repair-r2 rule witnesses `alphaY_falls_rule` / `alphaY_rises_rule`
show `α_Y` moving `2/3 → 1/2` and `1/3 → 1/2` along `Y₁ ⊑ Y₂`, both strictly past `H`. But the
package also proves `α_H = 0` under the rule (`alphaY_rulePress_self`), and `alphaY` is a ratio of
nonnegative sums. So for *every* `Y` — refining `H` or not — `α_H ≤ α_Y`: the one-step form of
"exceeding the overseers raises `α`" (compare the overseers' own partition with any other) is
trivially true, and on both rule witnesses the first step past `H` *rises* strictly
(`0 → 2/3`, `0 → 1/3`). What the witnesses refute is monotonicity *past* `H`, not the sentence's
one-step reading. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrPositionFinds.AuditR3

open Finset FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
  Cleanroom.Corrigibility.CorrPositionFinds

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- `α_Y ≥ 0` always (a ratio of sums of masses; junk `0` when the denominator is `0`). -/
theorem alphaY_nonneg {ι : Type*} [DecidableEq ι] (μ : Distr Ω) (X : Ω → ℝ) (Pr : Finset Ω)
    (Y : Ω → ι) : 0 ≤ alphaY μ X Pr Y := by
  unfold alphaY
  exact div_nonneg (sum_nonneg fun ω _ => μ.nonneg ω) (sum_nonneg fun ω _ => μ.nonneg ω)

/-- **Under the rule, `α_H ≤ α_Y` for every `Y`** — the weakest static reading of "the overseers'
`α` rises as the agent exceeds them" holds for a trivial reason: `α_H = 0` by construction
(`alphaY_rulePress_self`) and `α_Y ≥ 0`. No refinement hypothesis is even needed. -/
theorem alphaY_rulePress_self_le {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (μ : Distr Ω)
    (X : Ω → ℝ) (H : Ω → κ) (Y : Ω → ι) :
    alphaY μ X (rulePress μ X H) H ≤ alphaY μ X (rulePress μ X H) Y := by
  rw [alphaY_rulePress_self]
  exact alphaY_nonneg μ X _ Y

/-- On the rule-fall witness the first step past `H` *rises*: `α_H = 0 < 2/3 = α_{Y₁}`; the fall
`2/3 → 1/2` is the second step `Y₁ → Y₂`, both strictly past `H`. -/
theorem fall_rule_first_step_rises :
    alphaY w4Uniform XFallRule (rulePress w4Uniform XFallRule yThreeOne) yThreeOne = 0 ∧
      alphaY w4Uniform XFallRule (rulePress w4Uniform XFallRule yThreeOne) yTwoOneOne = 2 / 3 ∧
      alphaY w4Uniform XFallRule (rulePress w4Uniform XFallRule yThreeOne) yThreeOne <
        alphaY w4Uniform XFallRule (rulePress w4Uniform XFallRule yThreeOne) yTwoOneOne := by
  have h0 := alphaY_rulePress_self w4Uniform XFallRule yThreeOne
  have h1 := alphaY_falls_rule.2.2.1
  exact ⟨h0, h1, by rw [h0, h1]; norm_num⟩

/-- On the rule-rise witness likewise: `α_H = 0 < 1/3 = α_{Yₐ}`. -/
theorem rise_rule_first_step_rises :
    alphaY w4Uniform XRiseRule (rulePress w4Uniform XRiseRule hCoarse) hCoarse = 0 ∧
      alphaY w4Uniform XRiseRule (rulePress w4Uniform XRiseRule hCoarse) yOneOneTwo = 1 / 3 ∧
      alphaY w4Uniform XRiseRule (rulePress w4Uniform XRiseRule hCoarse) hCoarse <
        alphaY w4Uniform XRiseRule (rulePress w4Uniform XRiseRule hCoarse) yOneOneTwo := by
  have h0 := alphaY_rulePress_self w4Uniform XRiseRule hCoarse
  have h1 := alphaY_rises_rule.2.2.1
  exact ⟨h0, h1, by rw [h0, h1]; norm_num⟩

/-- The junk end of `alphaY_rulePress_self`, named: when no `H`-cell has positive sum the
continue region at `H` is empty and `α_H = 0` is `0 / 0`, not a rate. On `X ≡ −1` (uniform `μ`,
`H = hCoarse`) every cell sum is `−1/2 < 0`, the rule presses everywhere, and `μ(R_H) = 0`. -/
theorem alphaY_rulePress_self_junk_end :
    (∑ ω ∈ contRegion w4Uniform (fun _ => (-1 : ℝ)) hCoarse, w4Uniform.mass ω) = 0 ∧
      alphaY w4Uniform (fun _ => (-1 : ℝ)) (rulePress w4Uniform (fun _ => (-1 : ℝ)) hCoarse) hCoarse = 0 := by
  refine ⟨?_, alphaY_rulePress_self _ _ _⟩
  have hR : contRegion w4Uniform (fun _ => (-1 : ℝ)) hCoarse = ∅ := by
    ext ω
    cases ω <;> simp [contRegion, cellOf, cellSum, sum_filter, W4.sum_eq, hCoarse, w4Uniform,
      w4Distr] <;> norm_num
  rw [hR, sum_empty]

end Cleanroom.Corrigibility.CorrPositionFinds.AuditR3
