import Cleanroom.Li.LiDiagonal.Pinned
import LogicalInduction.Construction.Statistics.HistoricalMaturity

/-!
# `li-diagonal` · TwoFaces: the two faces do not die together on the diagonal (T4)

lean-deference-050's claim, over FAF's diagonal: **pointwise tracking of the diagonal's truth
fails by `min p (1−p)` in the limit** (the price sits at `p`, the truth at `0` or `1`), **while every
generable divergent weighting is recurringly unbiased** (FAF's `thm:recurringunbiasedness` on the
sentence family). So "both faces die together" is false on the diagonal (lean-deference-050), and
C4's point (lean-deference-061) stands: the paper's `χ^p_n` hard-decides, is `0/1`, anti-inductive,
and its price converges — the scope note compared against an un-indexed liar FAF does not have.

Scope: single-market. The cross-process form over `DiagonalPair` is `partial` and not stated as a
theorem here (findings).
-/

namespace Cleanroom.Li.LiDiagonal

open LogicalInduction LO.Propositional Cleanroom.Found.LiAsympCalc
open Filter Topology

/-- The diagonal's truth stream is a `TheoryTruth` (every completed world pays `diagTruth`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem diag_theoryTruth (P : History) (DP : DeductiveProcess) (p : ℚ)
    (q : ParadoxResistanceQuote P DP p) :
    AffineCombination.TheoryTruth q.sentence DP (diagTruth P q.sentence p) := by
  intro n v hv
  unfold PCWorld.payout diagTruth
  by_cases hlt : P n (q.sentence n) < (p : ℝ)
  · rw [if_pos ((q.diagonal_reflected n v hv).2 hlt), if_pos hlt]
  · rw [if_neg (fun h => hlt ((q.diagonal_reflected n v hv).1 h)), if_neg hlt]

/-- **T4 (headline). Two faces do not die together on the diagonal**: (i) pointwise, for every
`ε > 0`, eventually `min p (1−p) − ε ≤ |P_n(χ_n) − truth n|` — tracking the diagonal's truth
fails by `min p (1−p)` in the limit; (ii) averaged, every generable divergent weighting `W` has `0`
as a limit point of the weighted bias of `P_n(χ_n)` against `truth` (FAF's
`thm:recurringunbiasedness`). Here `truth n = 𝟙[P_n(χ_n) < p]` is the completed-theory truth of
`χ_n` (`diag_theoryTruth`).
Scope: single-market; threshold `p`; FAF's same-day diagonal (any `ParadoxResistanceQuote`).
Source: [[lean-deference-inventory]] 050, 061; [[li-diagonal-mandate]] T4
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem two_faces_diagonal (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1) (q : ParadoxResistanceQuote P DP p)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
      min (p : ℝ) (1 - p) - ε ≤ |P n (q.sentence n) - diagTruth P q.sentence p n|) ∧
    ∀ W : ℕ → EF, PGenerableWeighting W → DivergentWeighting W P →
      HasLimitPoint (weightedBias (fun i => (W i).denote P) (fun i => P i (q.sentence i))
        (diagTruth P q.sentence p)) 0 := by
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  constructor
  · intro ε hε
    filter_upwards [paradox_pinned_within_width P DP p hp0 hp1 q hworld,
      q.width_tendsto_zero (Iio_mem_nhds hε)] with n hn hw
    have hw' : (q.width n : ℝ) < ε := hw
    obtain ⟨hlo, hhi⟩ := abs_lt.1 hn
    unfold diagTruth
    by_cases hlt : P n (q.sentence n) < (p : ℝ)
    · rw [if_pos hlt, abs_of_nonpos (by linarith [(hP n (q.sentence n)).2])]
      linarith [min_le_right (p : ℝ) (1 - p)]
    · rw [if_neg hlt, sub_zero, abs_of_nonneg (hP n (q.sentence n)).1]
      linarith [min_le_left (p : ℝ) (1 - p)]
  · intro W hWgen hWdiv
    exact AffineCombination.recurringunbiasedness q.sentence
      (AffineCombination.sentenceAffine_polySequence q.sentence q.sentence_codes) hWgen
      (diag_theoryTruth P DP p q) hWdiv hworld

end Cleanroom.Li.LiDiagonal
