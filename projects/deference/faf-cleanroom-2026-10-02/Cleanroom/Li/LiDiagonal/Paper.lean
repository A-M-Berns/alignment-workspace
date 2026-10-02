import Cleanroom.Li.LiDiagonal.Pinned
import Cleanroom.Li.LiDiagonal.Engine
import Cleanroom.Li.LiDiagonal.Deferred
import Cleanroom.Li.LiDiagonal.Grade
import Cleanroom.Li.LiDiagonal.TwoFaces
import Cleanroom.Li.LiDiagonal.PastPrice
import LogicalInduction.Construction.Paper.Market

/-!
# `li-diagonal` · Paper: the N+ witnesses over FAF's paper market

Every single-market headline of this package, instantiated at FAF's real construction: the
market `liaHistory (paperDP T)` of the paper's logical inductor over the paper's deductive process
`paperDP T`, with its quotation presentation `paperQuotationPresentation T`, its market program
`paperMarketComputation T`, and its Kleene diagonal `paperDiagonalQuoteCode T p` — which is
`kleeneDiag T (paperMarketComputation T) p` definitionally (`paperKleene_eq`). The `thm:ceu` and
`thm:st` quote packages that `Deferred.lean` takes as hypotheses are discharged here from FAF's
closed forms (`paperFutureQuoteCode`, `lic_no_expected_net_update_closed`, `lic_self_trust_closed`),
so the paper-market T5 statements carry **no** hypothesis beyond the e.c. certificate of the
deferred family — which is itself discharged at `succDeferral` (`paper_defDiag_present_price_succ`).

This is the only file of the package importing `Construction.Paper.Market` (plan §0.5).

Grades. T1/T2b: **N+** — the pinned family is FAF's genuine Kleene diagonal built from the market
program by Kleene's recursion theorem, at the harmonic width `1/(n+1)` and at `2⁻ⁿ`. Whether its
price sits *exactly* at `p` from some day on is E2 (open); the package does not claim
non-constancy of the price sequence. T5: **N+** at `succDeferral` (every hypothesis discharged;
the family is the Kleene diagonal reindexed by `n+1`).
-/

namespace Cleanroom.Li.LiDiagonal

open LogicalInduction LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment LO.Propositional
open Cleanroom.Found.LiAsympCalc
open Filter Topology

section Paper

variable (T : ArithmeticTheory) [T.Δ₁] [Entailment.Consistent T] [𝗜𝚺₁ ⪯ T]

/-- FAF's `paperDiagonalQuoteCode` is `kleeneDiag` at the paper market.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma paperKleene_eq (p : ℚ) :
    kleeneDiag T (paperMarketComputation T) p =
      (paperDiagonalQuoteCode T p).toBooleanQuoteCode.sentence := rfl

/-! ## T1 witnesses -/

/-- **T1 over the paper market, every e.c. rate** (N+): for every e.c. `width → 0`, eventually
`|P_n(ψ_n) − p| < width n` on FAF's `LIA` over `paperDP T` at its own Kleene diagonal.
Scope: single-market; threshold `p`; FAF's same-day Kleene diagonal over the paper market.
Source: [[vq-wiki-2-inventory]] 014; [[li-diagonal-mandate]] T1 witness
Kind: N+
Fidelity: exact (instance of `paradox_pinned_every_rate`)
Hyps: (a) none (`hwidth` is the rate's own certificate) -/
theorem paper_pinned_every_rate (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (width : ℕ → ℚ) (hwidth : MachineRatCodes (fun n => 1 / width n))
    (hwidthPos : ∀ n, 0 < width n)
    (hwidthZero : Tendsto (fun n => (width n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      |liaHistory (paperDP T) n (kleeneDiag T (paperMarketComputation T) p n) - (p : ℝ)|
        < (width n : ℝ) :=
  haveI : 𝗣𝗔⁻ ⪯ T := inferInstance
  haveI := paperLIA T
  paradox_pinned_every_rate (paperQuotationPresentation T) (liaHistory (paperDP T))
    (paperMarketComputation T) p hp0 hp1 (paperDP_hworld T) width hwidth hwidthPos hwidthZero

/-- **T1 over the paper market at the harmonic rate** (N+): eventually
`|P_n(ψ_n) − p| < 1/(n+1)`.
Scope: single-market; threshold `p`; FAF's Kleene diagonal over the paper market.
Source: [[li-diagonal-mandate]] T1 witness
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem paper_pinned_harmonic (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ᶠ n in atTop,
      |liaHistory (paperDP T) n (kleeneDiag T (paperMarketComputation T) p n) - (p : ℝ)|
        < 1 / ((n : ℝ) + 1) := by
  haveI : 𝗣𝗔⁻ ⪯ T := inferInstance
  haveI := paperLIA T
  have h := paradox_pinned_within_width (liaHistory (paperDP T)) (paperDP T) p hp0 hp1
    (harmonicDiagonalQuote (paperQuotationPresentation T) (paperMarketComputation T) p)
    (paperDP_hworld T)
  filter_upwards [h] with n hn
  have hc : (((1 / ((n : ℚ) + 1) : ℚ) : ℝ)) = 1 / ((n : ℝ) + 1) := by push_cast; ring
  rw [← hc]
  exact hn

/-- **T1 over the paper market at the rate `2⁻ⁿ`** (N+): eventually `|P_n(ψ_n) − p| < 2⁻ⁿ`,
the paper's own tolerance sequence (`machineRatCodes_two_pow_inv`).
Scope: single-market; threshold `p`; FAF's Kleene diagonal over the paper market.
Source: [[li-diagonal-mandate]] T1 witness
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem paper_pinned_two_pow (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ᶠ n in atTop,
      |liaHistory (paperDP T) n (kleeneDiag T (paperMarketComputation T) p n) - (p : ℝ)|
        < (((((2 ^ n : ℕ) : ℚ))⁻¹ : ℚ) : ℝ) :=
  paper_pinned_every_rate T p hp0 hp1 (fun n => (((2 ^ n : ℕ) : ℚ))⁻¹)
    (machineRatCodes_two_pow_inv.inv_of_pos (fun n => by positivity))
    (fun n => by positivity)
    (Filter.Tendsto.congr (fun n => by push_cast; rw [inv_pow])
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num :
        ((2 : ℝ)⁻¹) < 1)))

/-! ## T2b witness -/

/-- **The pinning engine on the paper market's Kleene diagonal** (N+): `𝔼_n(𝟙ψ_n) → p` on
`liaHistory (paperDP T)`, every hypothesis of `pinning_engine` discharged on the real construction.
Scope: single-market; threshold `p`; FAF's Kleene diagonal over the paper market.
Source: [[li-diagonal-mandate]] T2b witness
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem paper_engine_diagonal (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1) :
    (fun n => (LUV.indicatorOf (kleeneDiag T (paperMarketComputation T) p n)).expect
      (liaHistory (paperDP T)) n) ≈ₙ fun _ => (p : ℝ) :=
  haveI : 𝗣𝗔⁻ ⪯ T := inferInstance
  haveI := paperLIA T
  pinning_engine_diagonal (liaHistory (paperDP T)) (paperDP T) p hp0 hp1
    (harmonicDiagonalQuote (paperQuotationPresentation T) (paperMarketComputation T) p)
    (paperDP_hworld T)

/-! ## T5 witnesses -/

/-- **T5c over the paper market** (N+): `P_n(χ_n) → p` for the deferred liar
`χ := defDiag ψ f` of the paper market's Kleene diagonal, with the `thm:ceu` package discharged
by FAF's `paperFutureQuoteCode` and `lic_no_expected_net_update_closed`. The only hypothesis is
the e.c. certificate of the deferred family (discharged at `succDeferral` below).
Scope: single-market; threshold `p`, deferral `f`; `defDiag` of the paper market's Kleene diagonal.
Source: [[weak-endorsement-deference-model]] §2.2; [[li-diagonal-mandate]] T5c witness
Kind: N+
Fidelity: exact
Hyps: (a) `hχ` (K9; `(a)` at `succDeferral`) -/
theorem paper_defDiag_present_price (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1) (f : DeferralFunction)
    (hχ : MachineSentenceCodes (defDiag (kleeneDiag T (paperMarketComputation T) p) f)) :
    (fun n => liaHistory (paperDP T) n
      (defDiag (kleeneDiag T (paperMarketComputation T) p) f n)) ≈ₙ fun _ => (p : ℝ) :=
  haveI : 𝗣𝗔⁻ ⪯ T := inferInstance
  haveI := paperLIA T
  defDiag_present_price_of_ceu (paperQuotationPresentation T) (liaHistory (paperDP T))
    (paperMarketComputation T) p f hp0 hp1 (paperDP_hworld T)
    (paperFutureQuoteCode T f _ hχ).luv (paperFutureQuoteCode T f _ hχ).poly
    (fun n v hv => by
      have h := RationalQuoteCode.reflected (paperQuotationPresentation T)
        (paperFutureQuoteCode T f _ hχ) n v hv
      rwa [← (paperMarketComputation T).quote_exact (f.f n) _] at h)
    (lic_no_expected_net_update_closed T f _ hχ)

/-- **T5c over the paper market at `succDeferral`** (N+, no hypotheses): `P_n(ψ_{n+1}) → p`.
Scope: single-market; threshold `p`, deferral `n ↦ n+1`; `defDiag` of the paper market's Kleene diagonal.
Source: [[li-diagonal-mandate]] T5c witness
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem paper_defDiag_present_price_succ (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1) :
    (fun n => liaHistory (paperDP T) n
      (defDiag (kleeneDiag T (paperMarketComputation T) p) succDeferral n)) ≈ₙ
      fun _ => (p : ℝ) :=
  paper_defDiag_present_price T p hp0 hp1 succDeferral
    (defDiag_codes_succ (kleeneDiag_codes T (paperMarketComputation T) p))

/-- **T5d over the paper market** (N+): `P_n(∼χ_n) → 1 − p`.
Scope: single-market; threshold `p`, deferral `f`.
Source: [[trust-lab-2-inventory]] 024; [[li-diagonal-mandate]] T5d witness
Kind: N+
Fidelity: exact
Hyps: (a) `hχ` (K9; `(a)` at `succDeferral`) -/
theorem paper_defDiag_neg_price (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1) (f : DeferralFunction)
    (hχ : MachineSentenceCodes (defDiag (kleeneDiag T (paperMarketComputation T) p) f)) :
    (fun n => liaHistory (paperDP T) n
      (∼ defDiag (kleeneDiag T (paperMarketComputation T) p) f n)) ≈ₙ fun _ => 1 - (p : ℝ) :=
  haveI : 𝗣𝗔⁻ ⪯ T := inferInstance
  haveI := paperLIA T
  neg_price_of_pos (liaHistory (paperDP T)) (paperDP T) _ hχ (paperDP_hworld T) p
    (paper_defDiag_present_price T p hp0 hp1 f hχ)

/-- **T5e over the paper market** (the note's no-go confirmed; N+): hard two-sided endorsement fails on the deferred
liar at `p = ½` on FAF's `LIA` over `paperDP T`, with every package discharged.
Scope: single-market; threshold `½`, deferral `f`.
Source: [[trust-lab-inventory]] 023; [[li-diagonal-mandate]] T5e witness
Kind: N+
Fidelity: exact (value-vs-demand reading)
Hyps: (a) `hχ` (K9; `(a)` at `succDeferral`) -/
theorem paper_hard_endorsement_fails (f : DeferralFunction)
    (hχ : MachineSentenceCodes (defDiag (kleeneDiag T (paperMarketComputation T) (1 / 2)) f)) :
    ¬ ((fun n => liaHistory (paperDP T) n
          (defDiag (kleeneDiag T (paperMarketComputation T) (1 / 2)) f n ⋏
            ∼ defDiag (kleeneDiag T (paperMarketComputation T) (1 / 2)) f n)) ≈ₙ
        fun n => (1 / 2 : ℝ) * liaHistory (paperDP T) n
          (∼ defDiag (kleeneDiag T (paperMarketComputation T) (1 / 2)) f n)) :=
  haveI : 𝗣𝗔⁻ ⪯ T := inferInstance
  haveI := paperLIA T
  hard_endorsement_fails_of_half (liaHistory (paperDP T)) (paperDP T) _ hχ (paperDP_hworld T)
    (paper_defDiag_present_price T (1 / 2) (by norm_num) (by norm_num) f hχ)

/-- **T5e over the paper market at `succDeferral`** (the note's no-go confirmed; N+, no hypotheses).
Scope: single-market; threshold `½`, deferral `n ↦ n+1`.
Source: [[trust-lab-inventory]] 023; [[li-diagonal-mandate]] T5e witness
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem paper_hard_endorsement_fails_succ :
    ¬ ((fun n => liaHistory (paperDP T) n
          (defDiag (kleeneDiag T (paperMarketComputation T) (1 / 2)) succDeferral n ⋏
            ∼ defDiag (kleeneDiag T (paperMarketComputation T) (1 / 2)) succDeferral n)) ≈ₙ
        fun n => (1 / 2 : ℝ) * liaHistory (paperDP T) n
          (∼ defDiag (kleeneDiag T (paperMarketComputation T) (1 / 2)) succDeferral n)) :=
  paper_hard_endorsement_fails T succDeferral
    (defDiag_codes_succ (kleeneDiag_codes T (paperMarketComputation T) (1 / 2)))

/-- **T5f over the paper market**: FAF's `thm:st` closed form at `φ := χ`, constant width `δ`
and constant threshold `p'` — soft one-sided self-trust on the deferred liar with every package
discharged by FAF's `paperConfidenceQuoteCode`.
Scope: single-market; threshold `p`, deferral `f`; `defDiag` of the paper market's Kleene diagonal.
Source: [[trust-lab-inventory]] 024; [[li-diagonal-mandate]] T5f witness
Kind: N+
Fidelity: exact (FAF's `lic_self_trust_closed` instance)
Hyps: (a) `hχ` (K9; `(a)` at `succDeferral`) -/
theorem paper_soft_self_trust (p : ℚ) (f : DeferralFunction)
    (hχ : MachineSentenceCodes (defDiag (kleeneDiag T (paperMarketComputation T) p) f))
    (δ p' : ℚ) (hδ : 0 < δ) (hp' : 0 ≤ p' ∧ p' ≤ 1) :
    (fun n ↦ (indicatorProductLUV
          (paperConfidenceQuoteCode T f (defDiag (kleeneDiag T (paperMarketComputation T) p) f)
            hχ (fun _ => δ) (fun _ => p') (MachineRatCodes.const δ).computable
            (PGenerableRat.ofMachineRatCodes (MachineRatCodes.const p') _))
          (defDiag (kleeneDiag T (paperMarketComputation T) p) f) n).expect
        (liaHistory (paperDP T)) n) ≳ₙ
      fun n ↦ (p' : ℝ) *
        ((paperConfidenceQuoteCode T f (defDiag (kleeneDiag T (paperMarketComputation T) p) f)
            hχ (fun _ => δ) (fun _ => p') (MachineRatCodes.const δ).computable
            (PGenerableRat.ofMachineRatCodes (MachineRatCodes.const p') _)).luv n).expect
          (liaHistory (paperDP T)) n :=
  haveI : 𝗣𝗔⁻ ⪯ T := inferInstance
  lic_self_trust_closed T f _ (fun _ => δ) (fun _ => p') (fun _ => hδ) (fun _ => hp') hχ
    (MachineRatCodes.const δ) (PGenerableRat.ofMachineRatCodes (MachineRatCodes.const p') _)

/-! ### T5f's N+ grading over the paper market (continuation) -/

/-- FAF's confidence quote code of `lic_self_trust_closed` for the deferred liar at
`f := succDeferral`, constant width `δ` and constant threshold `p'`; its `luv` is `thm:st`'s
`B_n`, and `indicatorProductLUV` of it is `A_n`.
Source: FAF `paperConfidenceQuoteCode`; [[li-diagonal-mandate]] T5f witness
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def paperLiarConfidence (p δ p' : ℚ) :=
  paperConfidenceQuoteCode T succDeferral
    (defDiag (kleeneDiag T (paperMarketComputation T) p) succDeferral)
    (defDiag_codes_succ (kleeneDiag_codes T (paperMarketComputation T) p))
    (fun _ => δ) (fun _ => p') (MachineRatCodes.const δ).computable
    (PGenerableRat.ofMachineRatCodes (MachineRatCodes.const p') (liaHistory (paperDP T)))

/-- **T5f's N+ product side over the paper market** (no hypotheses beyond `p' + δ < p`): FAF's
own product LUV `A_n` of `lic_self_trust_closed` has `𝔼_n(A_n) → p` on the deferred liar at
`succDeferral`.
Scope: single-market; threshold `p`, deferral `n+1`; `defDiag` of the paper market's Kleene diagonal.
Source: [[trust-lab-inventory]] 024; [[li-diagonal-mandate]] T5f witness
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem paper_product_expect_tendsto (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1) (δ p' : ℚ)
    (hδ : 0 < δ) (hlt : p' + δ < p) :
    (fun n ↦ (indicatorProductLUV (paperLiarConfidence T p δ p')
          (defDiag (kleeneDiag T (paperMarketComputation T) p) succDeferral) n).expect
        (liaHistory (paperDP T)) n) ≈ₙ fun _ => (p : ℝ) := by
  haveI : 𝗣𝗔⁻ ⪯ T := inferInstance
  haveI := paperLIA T
  refine product_expect_tendsto_p (paperQuotationPresentation T) (liaHistory (paperDP T))
    (paperMarketComputation T) p succDeferral hp0 hp1 δ p' hδ hlt _ (paperDP_hworld T)
    (indicatorProductLUV_machineThresholdCodeSeq _
      (defDiag_codes_succ (kleeneDiag_codes T (paperMarketComputation T) p)))
    (fun n v hv => ?_) (defDiag_codes_succ (kleeneDiag_codes T (paperMarketComputation T) p))
    (paper_defDiag_present_price_succ T p hp0 hp1)
  have h := indicatorProductLUV_valuesAt (paperQuotationPresentation T)
    (paperLiarConfidence T p δ p')
    (defDiag (kleeneDiag T (paperMarketComputation T) p) succDeferral) n v hv
  rwa [← paperConfidence_value_cast T succDeferral _ (fun _ => δ) (fun _ => p') n] at h

/-- **T5f graded N+ over the paper market** (no hypotheses beyond `0 < p'`, `p' + δ < p`): both
sides of `lic_self_trust_closed`'s instance on the deferred liar have positive limits `p` and
`p'`, with `p' < p`. At `p = ½`, `p' = ¼`, `δ < ¼` this is the mandate's N+ instance.
Scope: single-market; threshold `p`, deferral `n+1`.
Source: [[trust-lab-inventory]] 024; [[li-diagonal-mandate]] T5f ("at `p' = ¼` both sides have positive limits")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem paper_soft_self_trust_nondegenerate (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1) (δ p' : ℚ)
    (hδ : 0 < δ) (hp'0 : 0 < p') (hlt : p' + δ < p) :
    Tendsto (fun n ↦ (indicatorProductLUV (paperLiarConfidence T p δ p')
          (defDiag (kleeneDiag T (paperMarketComputation T) p) succDeferral) n).expect
        (liaHistory (paperDP T)) n) atTop (𝓝 (p : ℝ)) ∧
      Tendsto (fun n ↦ (p' : ℝ) * ((paperLiarConfidence T p δ p').luv n).expect
        (liaHistory (paperDP T)) n) atTop (𝓝 (p' : ℝ)) ∧
      (0 : ℝ) < p' ∧ (p' : ℝ) < p := by
  haveI : 𝗣𝗔⁻ ⪯ T := inferInstance
  haveI := paperLIA T
  refine soft_self_trust_nondegenerate (paperQuotationPresentation T) (liaHistory (paperDP T))
    (paperMarketComputation T) p succDeferral hp0 hp1 δ p' hδ hp'0 hlt _ _ (paperDP_hworld T)
    (indicatorProductLUV_machineThresholdCodeSeq _
      (defDiag_codes_succ (kleeneDiag_codes T (paperMarketComputation T) p)))
    (fun n v hv => ?_) (paperLiarConfidence T p δ p').poly (fun n v hv => ?_)
    (defDiag_codes_succ (kleeneDiag_codes T (paperMarketComputation T) p))
    (paper_defDiag_present_price_succ T p hp0 hp1)
  · have h := indicatorProductLUV_valuesAt (paperQuotationPresentation T)
      (paperLiarConfidence T p δ p')
      (defDiag (kleeneDiag T (paperMarketComputation T) p) succDeferral) n v hv
    rwa [← paperConfidence_value_cast T succDeferral _ (fun _ => δ) (fun _ => p') n] at h
  · have h := RationalQuoteCode.reflected (paperQuotationPresentation T)
      (paperLiarConfidence T p δ p') n v hv
    rwa [← paperConfidence_value_cast T succDeferral _ (fun _ => δ) (fun _ => p') n] at h

/-! ### T4 and T6a witnesses over the paper market (repair round 1) -/

/-- **T4 over the paper market** (N+): both faces of `two_faces_diagonal` on FAF's `LIA` over
`paperDP T` at its own Kleene diagonal (harmonic width): pointwise tracking of the diagonal's
truth fails by `min p (1−p)`, every generable divergent weighting is recurringly unbiased.
Scope: single-market; threshold `p`; FAF's Kleene diagonal over the paper market.
Source: [[lean-deference-inventory]] 050, 061; [[li-diagonal-mandate]] T4 (audit r1 N5/N8)
Kind: N+
Fidelity: exact (instance of `two_faces_diagonal`)
Hyps: (a) none -/
theorem paper_two_faces (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
      min (p : ℝ) (1 - p) - ε ≤
        |liaHistory (paperDP T) n (kleeneDiag T (paperMarketComputation T) p n) -
          diagTruth (liaHistory (paperDP T)) (kleeneDiag T (paperMarketComputation T) p) p n|) ∧
    ∀ W : ℕ → EF, PGenerableWeighting W → DivergentWeighting W (liaHistory (paperDP T)) →
      HasLimitPoint (weightedBias (fun i => (W i).denote (liaHistory (paperDP T)))
        (fun i => liaHistory (paperDP T) i (kleeneDiag T (paperMarketComputation T) p i))
        (diagTruth (liaHistory (paperDP T)) (kleeneDiag T (paperMarketComputation T) p) p)) 0 := by
  haveI : 𝗣𝗔⁻ ⪯ T := inferInstance
  haveI := paperLIA T
  exact two_faces_diagonal (liaHistory (paperDP T)) (paperDP T) p hp0 hp1
    (harmonicDiagonalQuote (paperQuotationPresentation T) (paperMarketComputation T) p)
    (paperDP_hworld T)

/-- **T6a's N+ witness over the paper market, constant threshold**: `gated_forcing_pastPrice_const`
on FAF's `LIA` over `paperDP T` — the gate on yesterday's price of the Kleene diagonal is
eventually `1`, the quote `X_n := ⌜r < P_{n−1}(ψ_{n−1})⌝` is eventually true, Lemma F holds, and
`P_n(X_n) → 1`. No hypotheses beyond `r + 2δ < p`.
Scope: single-market; threshold `p`; the paper market's Kleene diagonal read at yesterday.
Source: [[li-diagonal-mandate]] T6a instance (`Paper.lean`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem paper_gated_forcing_pastPrice_const (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (r δ : ℚ) (hδ : 0 < δ) (hr : r + 2 * δ < p) :
    (∀ n, (pastPriceRamp (kleeneDiag T (paperMarketComputation T) p) (fun n => n - 1) (fun _ => r)
        δ n).denote (liaHistory (paperDP T)) ≠ 0 →
      ∀ v : PCWorld, v.ConsistentWithTheory (paperDP T) →
        v.Holds ((pastPriceQuote T (paperMarketComputation T) p predComputable
          (Computable.const r)).sentence n)) ∧
    (∀ᶠ n in atTop,
      (pastPriceRamp (kleeneDiag T (paperMarketComputation T) p) (fun n => n - 1) (fun _ => r)
        δ n).denote (liaHistory (paperDP T)) = 1) ∧
    (∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory (paperDP T) →
      v.Holds ((pastPriceQuote T (paperMarketComputation T) p predComputable
        (Computable.const r)).sentence n)) ∧
    ((fun n => (pastPriceRamp (kleeneDiag T (paperMarketComputation T) p) (fun n => n - 1)
        (fun _ => r) δ n).denote (liaHistory (paperDP T)) *
      (1 - liaHistory (paperDP T) n ((pastPriceQuote T (paperMarketComputation T) p
        predComputable (Computable.const r)).sentence n))) ≈ₙ fun _ => 0) ∧
    Tendsto (fun n => liaHistory (paperDP T) n ((pastPriceQuote T (paperMarketComputation T) p
      predComputable (Computable.const r)).sentence n)) atTop (𝓝 1) := by
  haveI : 𝗣𝗔⁻ ⪯ T := inferInstance
  haveI := paperLIA T
  exact gated_forcing_pastPrice_const T (paperMarketComputation T) p
    (paperQuotationPresentation T) hp0 hp1 r δ hδ hr (paperDP_hworld T)

/-- **T6a's N+ witness over the paper market, alternating threshold**:
`gated_forcing_pastPrice_alternating` on FAF's `LIA` over `paperDP T` — the legal gate on
yesterday's price of the Kleene diagonal is eventually `1` exactly on the even days, the quote
family is eventually true exactly there, Lemma F and its mirror hold, and
`P_{2k}(X_{2k}) → 1`, `P_{2k+1}(X_{2k+1}) → 0`. No hypotheses beyond `r₀ + 2δ < p < r₁ − 2δ`.
Scope: single-market; threshold `p`; the paper market's Kleene diagonal read at yesterday.
Source: [[li-diagonal-mandate]] T6a instance (`Paper.lean`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem paper_gated_forcing_pastPrice_alternating (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (r₀ r₁ δ : ℚ) (hδ : 0 < δ) (hr₀ : r₀ + 2 * δ < p) (hr₁ : p + 2 * δ < r₁) :
    let r : ℕ → ℚ := fun n => if Even n then r₀ else r₁
    let ψ := kleeneDiag T (paperMarketComputation T) p
    let X := (pastPriceQuote T (paperMarketComputation T) p predComputable
      (alternatingThreshold_computable r₀ r₁)).sentence
    let P := liaHistory (paperDP T)
    (∀ n, (pastPriceRamp ψ (fun n => n - 1) r δ n).denote P ≠ 0 →
      ∀ v : PCWorld, v.ConsistentWithTheory (paperDP T) → v.Holds (X n)) ∧
    (∀ n, (pastPriceRampNeg ψ (fun n => n - 1) r δ n).denote P ≠ 0 →
      ∀ v : PCWorld, v.ConsistentWithTheory (paperDP T) → ¬ v.Holds (X n)) ∧
    (∀ᶠ n in atTop, Even n →
      (pastPriceRamp ψ (fun n => n - 1) r δ n).denote P = 1 ∧
      (pastPriceRampNeg ψ (fun n => n - 1) r δ n).denote P = 0 ∧
      ∀ v : PCWorld, v.ConsistentWithTheory (paperDP T) → v.Holds (X n)) ∧
    (∀ᶠ n in atTop, ¬ Even n →
      (pastPriceRamp ψ (fun n => n - 1) r δ n).denote P = 0 ∧
      (pastPriceRampNeg ψ (fun n => n - 1) r δ n).denote P = 1 ∧
      ∀ v : PCWorld, v.ConsistentWithTheory (paperDP T) → ¬ v.Holds (X n)) ∧
    ((fun n => (pastPriceRamp ψ (fun n => n - 1) r δ n).denote P * (1 - P n (X n))) ≈ₙ
      fun _ => 0) ∧
    ((fun n => (pastPriceRampNeg ψ (fun n => n - 1) r δ n).denote P * P n (X n)) ≈ₙ
      fun _ => 0) ∧
    Tendsto (fun k => P (2 * k) (X (2 * k))) atTop (𝓝 1) ∧
    Tendsto (fun k => P (2 * k + 1) (X (2 * k + 1))) atTop (𝓝 0) := by
  haveI : 𝗣𝗔⁻ ⪯ T := inferInstance
  haveI := paperLIA T
  exact gated_forcing_pastPrice_alternating T (paperMarketComputation T) p
    (paperQuotationPresentation T) hp0 hp1 r₀ r₁ δ hδ hr₀ hr₁ (paperDP_hworld T)

end Paper

end Cleanroom.Li.LiDiagonal
