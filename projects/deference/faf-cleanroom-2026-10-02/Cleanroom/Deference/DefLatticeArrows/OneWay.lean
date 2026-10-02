import Cleanroom.Deference.DefLatticeArrows.TowerToTrust
import Cleanroom.Deference.DefLatticeArrows.Fold
import Cleanroom.Deference.DefLatticeArrows.ArgmaxValue
import LogicalInduction.Construction.Paper.TheoremDP
import LogicalInduction.Construction.Quotation.MarketQuoteCodes

/-!
# T13 — The one-way pair: quotes of a computable expert exist over the paper's process

Package `def-lattice-arrows`, file 14 (`extension`). The mandate asked for the first package
whose existence the first arrow needs — the quote `⌜E*(XW)⌝` of the product for
Tower ⟹ TT — to be *stated* over a general expert with a computable history and listed open.
It is **provable**: FAF's `RationalQuoteCode.ofComputable` builds a quote code over the
paper's process `paperDP T` for **any** total computable `[0,1]`-rational sequence, and a
`MarketComputation E.A` presentation of the expert's history (FAF's sense of a computable
market: an exact rational quote table with a program) makes the deferred-day expectation
sequence `n ↦ E*(X_n)` computable (`MarketComputation.expectQuoteAt_computable`) and exact
(`expectQuoteAt_cast`). So every e.c. sequence `X` has an e.c. quote `Y` reflecting `E*(X)` in
every `paperDP T`-consistent world — `QuotesAvailable (paperDP T) E` at grade (a) — for every
expert whose history is a computable market, the self-expert (`paperMarketComputation T`)
included (`Witness.quotesAvailable_self`).

What this does **not** give (still `li-quote-lane`'s): the product, band, gap and follower
LUVs (`RampQuotesAvailable`, `BandQuotesAvailable`, `GapPackagesAvailable`,
`ProbeMenusAvailable`), which are products of a source with a quote — FAF's `dd:mesh`
constructions, done for the paper market's own weights (`conditionalExpectationQuoteCode`)
but not instantiated here.
-/

namespace Cleanroom.Deference.DefLatticeArrows

open LogicalInduction Cleanroom.Found.DefLattice
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]

/-- **Quotes exist for a computable expert over the paper's process** (T13): for an expert
`E` over `paperDP T` whose history has a `MarketComputation` presentation, every e.c. `X` has
an e.c. `Y` reflecting `E*(X)` — `RationalQuoteCode.ofComputable` on the computable rational
sequence `n ↦ hm.expectQuoteAt X n (E.f n)`, exact by `expectQuoteAt_cast`.
Source: mandate T13; FAF `RationalQuoteCode.ofComputable`, `MarketComputation`
(`Framework/Criterion.lean`), `paperQuotationPresentation`
Kind: C
Fidelity: exact (over `paperDP T`; the expert's history any computable market)
Hyps: (a) — `hm : MarketComputation E.A` is the computability presentation (data) -/
theorem quotesAvailable_of_marketComputation (E : Expert (paperDP T))
    (hm : MarketComputation E.A) : QuotesAvailable (paperDP T) E := by
  intro X hX
  have hcomp : Computable fun n => hm.expectQuoteAt X n (E.f n) :=
    ((hm.expectQuoteAt_computable hX).comp (Computable.id.pair E.f.computable) : _)
  let q := RationalQuoteCode.ofComputable T hcomp (fun n => hm.expectQuoteAt_mem_Icc X n (E.f n))
  refine ⟨q.luv, q.poly, fun n v hv => ?_⟩
  have h := RationalQuoteCode.reflected (paperQuotationPresentation T) q n v hv
  rwa [← hm.expectQuoteAt_cast X n (E.f n)] at h

/-- **Product quotes exist for a computable expert**, at every weight function: the clause
`ProductQuotesAvailable` of T4, discharged (the product LUV `XW` of a `WeightQuote` is e.c.).
Source: mandate T13 ("the product quote for Tower ⟹ TT")
Kind: L
Fidelity: exact (over `paperDP T`)
Hyps: (a) `hm` -/
theorem productQuotesAvailable_of_marketComputation (E : Expert (paperDP T))
    (hm : MarketComputation E.A) (wt : ℝ → ℝ) : ProductQuotesAvailable (paperDP T) E wt :=
  fun _ _ XW _ q => quotesAvailable_of_marketComputation T E hm XW q.product_codes

/-- **Left-product quotes exist for a computable expert**: the clause `CondQuotesReflected` of
T3, discharged.
Source: mandate T13
Kind: L
Fidelity: exact (over `paperDP T`)
Hyps: (a) `hm` -/
theorem condQuotesReflected_of_marketComputation (E : Expert (paperDP T))
    (hm : MarketComputation E.A) : CondQuotesReflected (paperDP T) E :=
  fun _ _ Z _ _ q => quotesAvailable_of_marketComputation T E hm Z q.left_codes

end

end Cleanroom.Deference.DefLatticeArrows
