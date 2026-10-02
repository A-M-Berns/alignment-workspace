import LogicalInduction.Properties.UniversalSemimeasure

/-!
# `def-tracking-pin` · Usm: the one FAF-derivable BLP corollary (T10)

anson-2-024 records the bounded-loss-prediction (BLP) Theorems 1–2 of chat 11 (L905–930) as a
retracted direction — standard Solomonoff/Hutter dominance plus telescoping, retracted as research
the same day. As theorems over FAF they would be kind T over a dominance hypothesis, and are
recorded only (findings). The one FAF-derivable corollary is this file: from FAF's domination of
the universal semimeasure (`lic_domination_universalSemimeasure`, `thm:dus`: one constant `C > 0`
with `C · M(σ) ≤ P∞(⌜σ⌝)` for every prefix `σ`), the limiting prefix beliefs of an inductor have
**bounded log-loss** against every lower-semicomputable continuous semimeasure:
`log M(σ) − log P∞(⌜σ⌝) ≤ log (1/C)` uniformly in `σ` with `M(σ) > 0`. Kind L, (a) with FAF's own
premises (the presentation data `A`, `emit`, `B` FAF's theorem carries, and `hworld`). Single
market; no ledger. This is the only file importing `Properties/UniversalSemimeasure`.
-/

namespace Cleanroom.Deference.DefTrackingPin

open LogicalInduction

/-- **T10. Bounded log-loss of the limiting prefix beliefs against every lower-semicomputable
semimeasure:** for an inductor `P` over `DP` with FAF's bit-prefix presentation data, there is a
constant `C > 0` such that for every prefix `σ` of positive mass,
`log M(σ) − log (limitingBelief P ⌜σ⌝) ≤ log (1/C)`. From `lic_domination_universalSemimeasure`
(`thm:dus`) by `log` monotonicity: `C · M(σ) ≤ P∞(⌜σ⌝)` gives `M(σ)/P∞(⌜σ⌝) ≤ 1/C`. The corpus's
BLP Theorems 1–2 (chat 11 L905–930) are the same inequality with `ξ` a universal semimeasure and
`H` the predictor; FAF's theorem holds of every lower-semicomputable `M`, so this is their
limiting-belief shadow at grade (a). Single market.
Source: anson-2-024 (chat 11 L905–930, the "cheap (a)-graded extension" of the inventory); FAF `thm:dus` (`Properties/UniversalSemimeasure.lean`)
Kind: L
Fidelity: variant: the inductor's limiting beliefs on prefix sentences in place of the chat's sequential predictor; the telescoped cumulative form of BLP Theorem 2 is the prefix form here
Hyps: (a) none beyond FAF's own premises (`A`, `emit`, `B`: conclusion-free presentation data; `hworld`) -/
theorem limitingBelief_logLoss_bounded {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure} {B : BitPrefixSentences DP}
    (A : DUSApproximationPresentation M B) (emit : DUSThresholdEmission A)
    (P : History) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ, 0 < M.mass σ →
      Real.log (M.mass σ) - Real.log (limitingBelief P (B.prefixSentence σ)) ≤
        Real.log (1 / C) := by
  obtain ⟨C, hC, hdom⟩ := lic_domination_universalSemimeasure A emit P hworld
  refine ⟨C, hC, fun σ hσ => ?_⟩
  have h := hdom σ
  have hpos : 0 < limitingBelief P (B.prefixSentence σ) := lt_of_lt_of_le (mul_pos hC hσ) h
  rw [← Real.log_div (ne_of_gt hσ) (ne_of_gt hpos)]
  apply Real.log_le_log (div_pos hσ hpos)
  rw [div_le_iff₀ hpos, one_div, inv_mul_eq_div, le_div_iff₀ hC]
  linarith [mul_comm C (M.mass σ)]

end Cleanroom.Deference.DefTrackingPin
