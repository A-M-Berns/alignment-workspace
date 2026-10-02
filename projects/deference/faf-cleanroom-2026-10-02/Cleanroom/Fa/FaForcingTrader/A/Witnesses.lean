import Cleanroom.Fa.FaForcingTrader.A.Violation
import Cleanroom.Fa.FaTheoremA.Witnesses
import Cleanroom.Found.LiQuoteLane.PaperSelf

/-!
# `fa-forcing-trader` · angle A · Witnesses: the N+ instances

* **T4 on a real inductor.** `H := liaHistory (atomDP id x (·+1))` (fa-theorem-a's W2 object from
  `li-pseudorandom`: a logical inductor whose process decides `atom k` at stage `k + 1`), the
  fixed indicator LUV `w2X k`, lookahead `succDeferral`, schedule `linearSchedule 0`
  (`2, 4, 6, …`), weighting the bare schedule indicator (divergent). Every hypothesis of
  `hSideBridge` is discharged: a real inductor, FAF's real trader on it, a window-disjoint
  schedule. **Not established**: that the round-trip return is not identically zero on this
  instance (that would evaluate the LIA's prices) — graded N+ for the hypothesis package, N− for
  exercising the return.
* **The same-market instances of T3/T6/T7.** `A = H = liaHistory (paperDP 𝗜𝚺₁)` with
  li-quote-lane's `crossQuotePackage_paper_self` (FAF's Σ₁ quotation of `H`'s own deferred
  expectations of `cleanX`): the (L) hypothesis and v3's joint legibility are *theorems* here
  (`legibleOn_quote_self` on both factors), so every hypothesis of `v3Theorem1_of_jointLegible` is
  discharged and T3's conclusion is unconditional on this pair — N+ for T3's hypothesis package
  (the package is inhabited by real objects), **N− for content**: at `A = H` the conclusion also
  follows from `cee` (fa-theorem-a's `Cee.lean` pattern), as the mandate records for W3. The
  T6/T7 instances `theoremSS_paper_self` / `schedThresholdAbove_paper_self` are **conditionals
  on `hdiv`** (the gate's divergence, which this file does not derive), hence **N−**, not
  inhabitants (regraded in repair round 1 — audit r1 fidelity B2 / adversarial B1 — and in these
  docstrings in repair round 2, audit r2 fidelity B1): the full-package inhabitants are the main
  module `Witnesses`' `theoremSS_paper_self_top` / `schedThresholdAbove_paper_self_top` (content
  threshold, `hdiv` derived) and `_negOne` (sub-zero threshold). The two-market instance is T11
  (OPEN).
Heavy imports (`Construction.Paper.Market`, `li-pseudorandom`): this is the only file of the angle
importing them.
-/

namespace Cleanroom.Fa.FaForcingTrader.A

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Fa.FaTheoremA
  Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice
  Cleanroom.Fa.FaForcingTrader Filter Topology

/-! ## A. T4 on `li-pseudorandom`'s decided-atom inductor -/

/-- **T4 witness (N+ for the package).** On `H = liaHistory (atomDP id x (·+1))` for any
primitive recursive `x`, with the indicator of `atom k`, lookahead `n + 1`, schedule `2, 4, 6, …`
and the bare schedule indicator as the weighting: the `H`-side bridge holds — the scheduled
average of the realized round-trip cash tends to `0`. A real inductor and FAF's real trader; the
return's non-vanishing on this instance is not established (report).
Source: mandate T4 witness; fa-theorem-a W2 (`w2H`, `w2X`, `w2_inductorH`, `w2_hworldH`)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem hSideBridge_w2 {x : ℕ → Bool} (hx : Primrec x) (k : ℕ) :
    WeightedApprox (fun n => (scheduleIndicator (linearSchedule 0) n).denote (w2H x))
      (fun n => (bundle (fun _ => w2X k) n).price (w2H x) (succDeferral.f n))
      (fun n => (w2X k).expect (w2H x) n) :=
  haveI := w2_inductorH hx
  hSideBridge (machineThresholdCodeSeq_const (indicatorOf_machineThresholdCodes _))
    (w2_hworldH x) (windowDisjoint_succ_linear 0) (scheduleIndicator_pgenerable _)
    (fun n hn => scheduleIndicator_supported _ _ n hn) (scheduleIndicator_divergent _ _)

/-! ## B. The same-market instances over `paperDP 𝗜𝚺₁` -/

/-- The paper LIA over `paperDP 𝗜𝚺₁`, as both markets.
Source: li-quote-lane T2.3; fa-theorem-a W1 (`w1H`)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable abbrev selfH : History := liaHistory (paperDP 𝗜𝚺₁)

/-- FAF's Σ₁ quotation family of `H`'s own next-day expectations of `cleanX`.
Source: li-quote-lane `crossQuotePackage_paper_self`; FAF `paperDeferredExpectationQuoteCode`
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable abbrev selfY : ℕ → LUV :=
  (paperDeferredExpectationQuoteCode 𝗜𝚺₁ succDeferral cleanX cleanX_codes).luv

/-- The same-market quote package (li-quote-lane T2.3).
Source: li-quote-lane `crossQuotePackage_paper_self`
Kind: L
Fidelity: exact (same-market instance)
Hyps: (a) none -/
theorem self_pkg : CrossQuotePackage selfH (paperDP 𝗜𝚺₁) succDeferral cleanX selfY :=
  crossQuotePackage_paper_self 𝗜𝚺₁ succDeferral cleanX cleanX_codes

/-- **Joint legibility is a theorem at `A = H`**: every factor of the violation weight is a legal
feature of the single market (`legibleOn_quote_self` on the quote and on `cleanX`'s own
expectation, `LegibleOn.schedInd` for the schedule).
Source: mandate T3 witness ("at `A = H` … `violW` is `H`-native")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem self_jointLegible (d : DeferralFunction) (t ε : ℚ) {δ : ℚ} (hδ : 0 < δ) :
    LegibleOn selfH (violW d (quoteSeq selfY selfH) (fun n => (cleanX n).expect selfH n) t ε δ) :=
  ((LegibleOn.schedInd d selfH).mul
    (((legibleOn_quote_self selfY self_pkg.quote_codes selfH).rampAbove t hδ).mul
      ((legibleOn_quote_self cleanX cleanX_codes selfH).rampBelow (t - ε) hδ))).congr
    (fun n => (violW_eq d _ _ t ε δ n).symm)

/-- **T3 at the same-market instance, every hypothesis discharged** (N+ for the package, N− for
content: `A = H`). For every window-disjoint schedule for `succDeferral` and rationals
`t`, `ε > 0`, `δ > 0`, the violation mass of the paper LIA's quote of its own next-day
expectation of `cleanX` against its present expectation does not diverge.
Source: mandate T3 witness; li-quote-lane T2.3
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem v3Theorem1_paper_self {d : DeferralFunction} (hwd : WindowDisjoint succDeferral d)
    (t ε : ℚ) {δ : ℚ} (hδ : 0 < δ) (hε : 0 < ε) :
    ¬ Tendsto (prefixSum (violW d (quoteSeq selfY selfH) (fun n => (cleanX n).expect selfH n)
      t ε δ)) atTop atTop :=
  haveI := w1_inductorH
  v3Theorem1_of_jointLegible self_pkg cleanX_codes (paperDP_hworld 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁)
    (fun n v hv => indicatorOf_valued (witnessQuoted 0 n) _ v hv) hwd t ε hδ hε
    ⟨self_jointLegible d t ε hδ, self_jointLegible d t ε hδ⟩

/-- **T6 at the same-market instance, conditional on `hdiv`** (not an inhabitant): every
hypothesis of `theoremSS_limitPoint` but the gate's divergence is discharged, and `hdiv` is taken
as a hypothesis — this file does not derive it. **N−** (a conditional; regraded in repair round 1,
docstring corrected in repair round 2, audit r2 fidelity B1). The full-package inhabitants are
`theoremSS_paper_self_top` (`Witnesses`; `hdiv` derived at every content threshold `t + δ < 1` on
`X ≡ 𝟙(⊤)`) and `theoremSS_paper_self_negOne` (`t ≤ −δ`, where the gate is the whole schedule).
Source: mandate T6 witness
Kind: N− (conditional on `hdiv`)
Fidelity: n/a
Hyps: (a) `hdiv` (taken as a hypothesis here, not derived; derived in `Witnesses`) -/
theorem theoremSS_paper_self {d : DeferralFunction} (hwd : WindowDisjoint succDeferral d)
    (t : ℚ) {δ : ℚ} (hδ : 0 < δ) (hdiv : DivergentWeighting (schedGate selfY d t δ) selfH) :
    HasLimitPoint (weightedBias (fun n => (schedGate selfY d t δ n).denote selfH)
      (quoteSeq selfY selfH) (fun n => (cleanX n).expect selfH n)) 0 :=
  haveI := w1_inductorH
  theoremSS_limitPoint self_pkg cleanX_codes (paperDP_hworld 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁)
    (fun n v hv => indicatorOf_valued (witnessQuoted 0 n) _ v hv) hwd t hδ
    (legibleOn_quote_self selfY self_pkg.quote_codes selfH) hdiv

/-- **T7 at the same-market instance, conditional on `hdiv`** (not an inhabitant), same grading
as `theoremSS_paper_self`: **N−**. The full-package inhabitants are
`schedThresholdAbove_paper_self_top` (`Witnesses`) and `schedThresholdAbove_paper_self_negOne`.
Source: mandate T7 witness
Kind: N− (conditional on `hdiv`)
Fidelity: n/a
Hyps: (a) `hdiv` (taken as a hypothesis here, not derived; derived in `Witnesses`) -/
theorem schedThresholdAbove_paper_self {d : DeferralFunction}
    (hwd : WindowDisjoint succDeferral d) (t : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hdiv : DivergentWeighting (schedGate selfY d t δ) selfH) :
    SchedThresholdAbove (fun n => (schedGate selfY d t δ n).denote selfH)
      (fun n => (cleanX n).expect selfH n) t :=
  haveI := w1_inductorH
  schedThresholdAbove_of_theoremSS self_pkg cleanX_codes (paperDP_hworld 𝗜𝚺₁)
    (paperDP_hworld 𝗜𝚺₁) (fun n v hv => indicatorOf_valued (witnessQuoted 0 n) _ v hv) hwd t hδ
    (legibleOn_quote_self selfY self_pkg.quote_codes selfH) hdiv

end Cleanroom.Fa.FaForcingTrader.A
