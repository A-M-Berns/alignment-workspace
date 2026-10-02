import Cleanroom.Found.LiQuoteLane.Defs
import LogicalInduction.Construction.Paper.Market

/-!
# `li-quote-lane` · PaperSelf: the same-market instance of the cross-market quote package (T2.3)

Adopted from the round-1 fidelity probe (`audit-r1-probes/CrossQuoteSelfInstance.lean`, N3). The
report had said T2.3 was unavailable because "FAF exposes the closed theorem, not the structure";
that was wrong: FAF's `paperDeferredExpectationQuoteCode T f X hX` (`Construction/Paper/Market.lean`)
is a `RationalQuoteCode` whose `.luv` family is e.c. (`.poly`) and is reflected at
`(paperMarketComputation T).expectQuoteAt X n (f n)` in every completed-theory world of
`paperDP T` (`RationalQuoteCode.reflected` at `paperQuotationPresentation T`), which
`expectQuoteAt_cast` identifies with `(X n).expect (liaHistory (paperDP T)) (f n)`. So the package
at `H = A = liaHistory (paperDP T)` is a direct construction. **Graded N−**: one market (`H = A`),
as the mandate said is the best FAF gives without a second market; the two-market N+ is
`paperMirrorPair` (`Witnesses.lean`). Heavy import (`Construction.Paper.Market`): own file, not
imported by any other module of the package. Scope: one-way.
-/

namespace Cleanroom.Found.LiQuoteLane

open LogicalInduction LO LO.FirstOrder LO.Entailment

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]

/-- **T2.3 (N−). The same-market instance of `CrossQuotePackage`** over `paperDP T`: with
`Y := (paperDeferredExpectationQuoteCode T f X hX).luv`, `H = A = liaHistory (paperDP T)`, FAF's
Σ₁ quotation LUVs of `H`'s own deferred expectations form a `CrossQuotePackage`. `quote_codes`
is FAF's `.poly`; `reflected` is FAF's `.reflected` rewritten by `expectQuoteAt_cast`. N− because
the two markets coincide; the package's content (a *different* market reflecting `H`) is
exercised by `paperMirrorPair`.
Source: mandate T2.3; FAF `lic_expected_future_expectations_closed` / `paperDeferredExpectationQuoteCode`
Kind: N-
Fidelity: exact (same-market instance)
Hyps: (a) none -/
theorem crossQuotePackage_paper_self (f : DeferralFunction) (X : ℕ → LUV)
    (hX : LUV.MachineThresholdCodeSeq X) :
    CrossQuotePackage (liaHistory (paperDP T)) (paperDP T) f X
      (paperDeferredExpectationQuoteCode T f X hX).luv := by
  refine ⟨(paperDeferredExpectationQuoteCode T f X hX).poly, fun n v hv => ?_⟩
  rw [(paperMarketComputation T).expectQuoteAt_cast X n (f.f n)]
  exact (paperDeferredExpectationQuoteCode T f X hX).reflected (paperQuotationPresentation T)
    n v hv

end Cleanroom.Found.LiQuoteLane
