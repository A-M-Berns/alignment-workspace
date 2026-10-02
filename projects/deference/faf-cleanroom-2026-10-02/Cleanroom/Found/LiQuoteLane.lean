import Cleanroom.Found.LiQuoteLane.Defs
import Cleanroom.Found.LiQuoteLane.Ledger
import Cleanroom.Found.LiQuoteLane.Codes
import Cleanroom.Found.LiQuoteLane.Computability
import Cleanroom.Found.LiQuoteLane.Feature
import Cleanroom.Found.LiQuoteLane.Readability
import Cleanroom.Found.LiQuoteLane.PullBack
import Cleanroom.Found.LiQuoteLane.CrossQuote
import Cleanroom.Found.LiQuoteLane.OneWay
import Cleanroom.Found.LiQuoteLane.PaperWitness
import Cleanroom.Found.LiQuoteLane.MirrorPair
import Cleanroom.Found.LiQuoteLane.PaperQuotation
import Cleanroom.Found.LiQuoteLane.Witnesses
import Cleanroom.Found.LiQuoteLane.PaperSelf
import Cleanroom.Found.LiQuoteLane.Conditioning

/-!
# `li-quote-lane`: cross-market quotes and ledger-augmented deductive processes

Root module of the package `Cleanroom.Found.LiQuoteLane`; dependents import this one name (or
`Defs` alone, for the definitions of record). Mandate:
`run/wp/li-quote-lane/li-quote-lane-mandate.md`; report, findings and ledger beside it.

**Scope: one-way throughout** — `H` reads `A`, `A` is any fixed inductor. The two-way pair is
`li-coupled-pair`'s open row of record.

* `Defs`: the definitions of record — `PublicationSchedule` (weak; strict via
  `DeferralFunction.toPublicationSchedule`), `ledgerLuv` (family 3, day first), `ledgerSchedule`
  / `ledgerProcess` (the corpus's `DP_H ⊕ ledger` through `bli-found`'s `extendBy`),
  `CrossQuotePackage` (a Kind-D hypothesis package), `OneWayPair`, `ledgerFeature`, `pullBack`.
* `Ledger` (T1.2, T1.5): which threshold is decided by which stage; functionality with no
  hypothesis; `ledgerLuv_determinedVia` — the ledger LUV is determined at the published value
  — with its `li-asymp-calc` corollaries; `hworld` and conservativity re-exports.
* `Codes` (T1.3): `ledgerLuv_thresholdCodes`, the e.c. certificate of the ledger LUV family.
* `Computability` (T1.4): `ledgerProcess_computable`, the `Computable` (not `Primrec`)
  certificate a LIA quote table can meet.
* `Feature` (T4.2): `ledgerFeature_pgenerable` — the ledger price feature is a legal feature;
  the ramp `ledgerRamp` is legal and tracks the ramp of the published number within
  `|𝔼 − a|/δ`.
* `Readability` (T3): `readability_ofApprox` — [[route-recurring-ccee]] §2 Lemma 2.1 (ledger
  tracking) in approximant form: any `P`-generable rational `ẑ` with `ẑ_n − a_{j,n} → 0` makes
  the reader price the ledger LUV at the published number (the (c) `hz`: the relativized class
  has no FAF object; variant, plain trader class); `readability` (T3.1) is its instance at the
  exact approximant (L4 with (L) rendered as `PGenerableRat` of the table, `hL`),
  `readability_ofTendsto` at a constant one (a table with a rational limit needs no
  generability at all), `readability_ofMachineApprox` at `MachineRatCodes` approximants;
  `readability_fails_without_generability` (OPEN) states the failure of the (a)-only version;
  Lemma 3's outside half.
* `PullBack` (T5): `pullBack_pgenerable` — generable weightings pull back along a strictly
  increasing deferral function; `pullBackRat` is a legal `ccee` weight.
* `CrossQuote` (T2.2): the self-instance and the `DeterminedViaTheory` / `WorldValued` /
  mesh / `BoundedSequence` consequences of a `CrossQuotePackage`.
* `OneWay` (T6.1): `oneWayPair_inductor`, `OneWayPair.ofLIA` — the one-way pair exists, from
  FAF's LIA on both sides, no recursion; the family-of-schedules generator. The only file
  importing `Construction.LIACompiler`.
* `PaperWitness` (T6.2): `paperOneWayPair` over `paperDP 𝗜𝚺₁` (N+).
* `MirrorPair` (T2.4): `crossQuotePackage_mirror` — the package is a theorem over the mirror
  ledger (`A` records `H`'s realized expectations), with its inductor and the scope clause.
* `PaperQuotation` (T1.6, Route Q): `aQuoteCode`, `A`'s quote table as FAF's `RationalQuoteCode`
  over `paperDP T`, and `ledger_quote_alias` — the fresh ledger LUV and the Σ₁ quotation LUV
  are valued at the same number in every completed-theory world; `hworld` over `paperDP T`.
* `Witnesses` (repair rounds 1–2): `readability_unpair` — T3.1's full hypothesis package
  inhabited over `paperDP 𝗜𝚺₁` with FAF's LIA as reader at an oscillating table with no limit
  (N+ for the statement, the witness on which `hL` is load-bearing; N− for the LIA-table
  application), with `unpair_expect_not_convergent`; `readability_harmonic`,
  `readability_twoPowInv` (convergent tables: N− for `readability`, `hL` idle — their
  `_ofTendsto` twins prove the same with no `hL`); `cleanMirrorPair` (primary) and
  `paperMirrorPair` — T2.1's package with two distinct markets, `hworld`, a theory world, the
  inductor and the scope clause.
* `PaperSelf` (T2.3, N−): `crossQuotePackage_paper_self`, the same-market instance from FAF's
  `paperDeferredExpectationQuoteCode`. The only file importing `Construction.Paper.Market`.
* `Conditioning` (T6.3, stretch; repair round 1): anson-2-002's conditioning route with its
  certificate explicit — `ledgerSeq` (the ledger as a conditioning sequence),
  `conditioningRoute_inductor` (FAF's `lic_conditioned_growing_ofSequence` at it; the (c) is
  `MachineSentenceCodes (ledgerSeq a e)`, standing in for the source's cost-domination schedule),
  `ledgerLuv_determinedVia_conditioned` (T1.2 for the route), `ledgerConditionedProcess_theoryWorld`
  (non-vacuity from T1.5), `conditioningRoute_ofLIA`. The only file importing
  `Construction.Conditioning.Endpoints`.
-/
