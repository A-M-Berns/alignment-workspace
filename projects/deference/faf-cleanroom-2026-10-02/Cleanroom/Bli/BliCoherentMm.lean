import Cleanroom.Bli.BliCoherentMm.Worlds
import Cleanroom.Bli.BliCoherentMm.Waived
import Cleanroom.Bli.BliCoherentMm.FixedPoint
import Cleanroom.Bli.BliCoherentMm.Accept
import Cleanroom.Bli.BliCoherentMm.Maker
import Cleanroom.Bli.BliCoherentMm.Sat
import Cleanroom.Bli.BliCoherentMm.Contrast
import Cleanroom.Bli.BliCoherentMm.Recursion
import Cleanroom.Bli.BliCoherentMm.Witness
import Cleanroom.Bli.BliCoherentMm.Payoffs
import Cleanroom.Bli.BliCoherentMm.Omni
import Cleanroom.Bli.BliCoherentMm.AttemptA
import Cleanroom.Bli.BliCoherentMm.AttemptB

/-!
# `bli-coherent-mm`: the coherent fixed point, the coherent (interior, truth-respecting) market
maker, the propositionally coherent inductor — reconciled package

Root module of the dual package `bli-coherent-mm` (area `bli`, namespace
`Cleanroom.Bli.BliCoherentMm`), over `bli-finite` (`worldOf`, `IsWorldMarginal`, `CoherentOn`),
`bli-overlay` (`mentionedSet`, the value congruences, `restrictedPast`, the recursion pattern)
and FAF (`Strategy.value`, `PCWorld`, `FiniteWorld`, `candidateRationalHistory`,
`marketValueRat`, `MarketMakerAccepts`, `MarketMaker`, `TradingFirmAt`,
`trading_firm_dominance`, `stdSimplex_hasFPP`, `paperDP_hworld`). Two independent attempts
(`AttemptA/`: Nash's map, search by enumeration, priced set parametric; `AttemptB/`: the
clip-and-normalise map, the rounded fixed point on a mesh) both reached every core target and
the stretch target sorry-free; this package states each target once over the **definitions of
record** — attempt A's throughout (D1–D5), with attempt B's makers and recursion kept as the
**grid variant** and every attempt-B headline transported to the record's vocabulary — and
proves the cross-checks: the two attempts' worlds, measures, tables and candidate states are
the same objects (`Worlds`), their acceptance predicates are equivalent
(`coherentAccepts_iff_attemptB`), both makers pass the record's D3 although their candidates
differ (`coherentWeights_accepts`, `gridCoherentWeights_accepts`), T0/T1/T2(a)/T3(a)/T5 are
each proved by both routes, and both recursions inhabit the record's `PCInductor`.

* **Worlds** (D1, D2) — `WD`, `IsWorldMeasure`, `marginal`, `ofWeights`, `candidateTable`; the
  identifications with attempt B.
* **Waived** (T0) — `not_exploits_of_dayValue_le_consistent_off_finite` (stage-relative; two
  proofs) and its firm corollaries.
* **FixedPoint** (T1) — `coherent_fixed_point_abstract` (Soto's Theorem 2, finite form; two
  routes), **`coherent_fixed_point`** (headline: no atom bound, any prior history), the
  `PCWorld` form, the mandate's shape by both routes; the identity proved.
* **Accept** (D3, T2(a), T3(a), T2(d)) — `CoherentAccepts` (decidable), the cross-check,
  `exists_coherentAccepts`, `exists_coherentAccepts_fullSupport` (both routes), the entry point.
* **Maker** (D4, T2(b)–(e), T3) — `coherentMarketMaker`/`coherentWeights`,
  `interiorCoherentMarketMaker`/`interiorWeights` (enumeration search), their acceptance,
  coherence (`CoherentQuoteOn`), decided-at-truth, non-dogmatism, `interior_D_ND_day`; the grid
  makers `gridCoherentMarketMaker`/`gridInteriorCoherentMarketMaker` with the grid shape.
* **Sat** (T5) — `pos_iff_satisfiable` (two routes), the `PCWorld` form, at the interior maker.
* **Contrast** (T4(a)–(c)) — `marketMaker_incoherent_on_pair` (FAF's maker forced incoherent;
  finding of record), the coherent makers on the pair (N+), the responsive strategy (N+).
* **Recursion** (D5, T6) — `pcRec`, `pcCoreState`, `pcCoreWeights`, `pcQuote`, `pcHistory`,
  `pcFirmStrat`, **`pcOverlay_no_ec_trader_exploits`**, **`pcOverlay_coherent_mentioned`**,
  non-dogmatism, monotonicity, `D_PC_mentioned`, the assembly lemma (`ComputableMarket`
  assumed), `PCInductor` with `pcInductor` and the grid inhabitant `pcInductorGrid`.
* **Witness** (T4(d), T6's witness) — the package over `paperDP 𝗜𝚺₁`.
* **Payoffs** (T8, extension) — Soto's intermediate payoffs as finite arithmetic (`variant`).
* **Omni** (T7, extension) — the omni-trader fixed point over `ProbabilityMeasure` on the
  `D`-consistent Cantor worlds, stated **OPEN** (`omni_fixed_point`, the package's one `sorry`),
  with the finite-support reduction **proved** (`omni_fixed_point_of_finiteSupport`: a demand
  supported on a finite `S` and factoring through the marginal on `B` atoms has a fixed point,
  by T1's abstract lemma and a Dirac mixture).

**Honest status of T6** (Known issue 8): no e.c. trader exploits the coherent overlaid market;
it is exactly coherent on the priced set on every day whose stage has a consistent world (every
day, over `paperDP 𝗜𝚺₁`); **`ComputableMarket` is open** — nothing here is a logical inductor.
T7 (omni-traders, the infinite fixed point) is stated as OPEN in `Omni.lean` (neither attempt
stated it in Lean); the open part is exactly the infinitely-supported case.
-/
