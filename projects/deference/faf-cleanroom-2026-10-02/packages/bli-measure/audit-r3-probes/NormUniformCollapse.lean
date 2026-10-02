import Cleanroom.Bli.BliMeasure.Norm

/-!
# Audit r3 (adversarial) probe — the target-6 (d) open row at FAF's LIA

`normWeights_noExploit_open` quantifies over every logical inductor `P` over `DP` and every atom
bound `B` covering the day's small sentences and stage (`hB`, `hBD`). The package's N− for (b)
(`normSum_lia_eq_zero`) exhibits, per day, *one* bound beyond the LIA's day-`n` support at which
the normalizer vanishes. This probe shows the collapse is not special to that bound: at **every**
`B` beyond the atom bound of the day-`n` support the normalizer of FAF's LIA is `0`, the online
weights are the uniform measure on `FiniteWorld B`, and the sentence market the open row speaks
about is the uniform marginal `(1/2^B) · #{u ⊨ φ}` on that day. The remaining (argued, not
machine-checked) step of the finding is in the audit file: a covering `B n` dominates every
atom of the LIA's day-`n` support for all large `n`, so the induced market is uniform from some
day on and prices every non-tautological stage sentence at a constant `< 1` — which the constant
one-share-a-day buyer of that sentence exploits.

Not imported by the library.
-/

namespace Cleanroom.Bli.BliMeasure.AuditR3

open LogicalInduction LO.Propositional Finset BoolPCWorld Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliFound Cleanroom.Bli.BliMeasure

/-- At every atom bound `B` beyond the day-`n` support, the LIA's normalizer is `0`. -/
theorem normSum_lia_eq_zero_of_lt (DP : DeductiveProcess) (n B : ℕ) (hB : 0 < B)
    (h : (liaStates DP n).support.sup atomBound < B) :
    normSum (liaHistory DP) n B = 0 := by
  unfold normSum
  apply Finset.sum_eq_zero
  intro u _
  have hcast : liaHistory DP n (worldConj u) = (liaQuote DP n (worldConj u) : ℝ) := rfl
  have hq : liaQuote DP n (worldConj u) = 0 := by
    apply (liaStates DP n).quote_eq_zero_of_not_mem
    intro hmem
    have h1 := Finset.le_sup (f := atomBound) hmem
    have h2 := le_atomBound_worldConj hB u
    omega
  rw [hcast, hq, Rat.cast_zero]

/-- … so the online weights are the uniform default there. -/
theorem normWeights_lia_uniform_of_lt (DP : DeductiveProcess) (n B : ℕ) (hB : 0 < B)
    (h : (liaStates DP n).support.sup atomBound < B) (u : FiniteWorld B) :
    normWeights (liaHistory DP) n B u = 1 / (Fintype.card (FiniteWorld B) : ℝ) := by
  unfold normWeights
  rw [if_pos (normSum_lia_eq_zero_of_lt DP n B hB h)]

/-- … and the sentence market of `normWeights_noExploit_open` is the uniform marginal on day `n`. -/
theorem induced_market_uniform_of_lt (DP : DeductiveProcess) (n B : ℕ) (hB : 0 < B)
    (h : (liaStates DP n).support.sup atomBound < B) (φ : Sentence) :
    ∑ u : FiniteWorld B, normWeights (liaHistory DP) n B u * (worldOf u).payout φ =
      (1 / (Fintype.card (FiniteWorld B) : ℝ)) * ∑ u : FiniteWorld B, (worldOf u).payout φ := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [normWeights_lia_uniform_of_lt DP n B hB h u]

end Cleanroom.Bli.BliMeasure.AuditR3
