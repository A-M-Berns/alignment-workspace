import Cleanroom.Bli.BliCoherentMm.AttemptA.Worlds
import Cleanroom.Bli.BliCoherentMm.AttemptA.Waived
import Cleanroom.Bli.BliCoherentMm.AttemptA.FixedPoint
import Cleanroom.Bli.BliCoherentMm.AttemptA.Accept
import Cleanroom.Bli.BliCoherentMm.AttemptA.Maker
import Cleanroom.Bli.BliCoherentMm.AttemptA.Sat
import Cleanroom.Bli.BliCoherentMm.AttemptA.Contrast
import Cleanroom.Bli.BliCoherentMm.AttemptA.Recursion
import Cleanroom.Bli.BliCoherentMm.AttemptA.Witness
import Cleanroom.Bli.BliCoherentMm.AttemptA.Payoffs

/-!
# `bli-coherent-mm`, attempt A: the coherent fixed point, the coherent and interior market makers,
the propositionally coherent overlaid market — by Nash's map and search by enumeration

Root module of attempt A of the dual package `bli-coherent-mm` (area `bli`, namespace
`Cleanroom.Bli.BliCoherentMm.AttemptA`), over `bli-finite` (`worldOf`, `payoutRat_*`,
`IsWorldMarginal`, `twoAxiom_of_worldMarginal`), `bli-overlay` (`mentionedSet`, the value
congruences, `restrictedPast`, the recursion pattern, `firm_mentions_something_paperDP`) and FAF
(`Strategy.value`, `PCWorld`, `FiniteWorld`, `candidateRationalHistory`, `marketValueRat`,
`MarketMakerAccepts`, `MarketMaker`, `TradingFirmAt`, `trading_firm_dominance`,
`stdSimplex_hasFPP`, `paperDP_hworld`). Angle A: Nash's map on the `D`-consistent world simplex
for the fixed point; the maker is the first accepted candidate of a total enumeration of rational
weight vectors.

* **Worlds** (D1, D2) — `WD D B` (decidable filter), `IsWorldMeasure`, `marginal` (`π`),
  `ofWeights`, `candidateTable`, the restriction bridge `restrict_mem_WD` /
  `value_payout_eq_restrict`, and T2(c)'s engine `marginal_of_decided_true/false`.
* **Waived** (T0) — **`not_exploits_of_dayValue_le_consistent_off_finite`** (headline, the
  stage-relative waived-days lemma) and its firm corollaries.
* **FixedPoint** (T1) — `coherent_fixed_point_abstract` (Nash's map + Brouwer on `stdSimplex ℝ ι`,
  transported from FAF's `stdSimplex_hasFPP`), **`coherent_fixed_point`** (headline, over
  `FiniteWorld B`, the identity proved) and `coherent_fixed_point_pcWorld`.
* **Accept** (D3, T2(a), T3(a), T2(d)) — `CoherentAccepts` (decidable), the density lemma
  `exists_rat_simplex_near`, **`exists_coherentAccepts`**, **`exists_coherentAccepts_fullSupport`**,
  the entry point `dayValue_le_of_coherentAccepts` (+ split form).
* **Maker** (D4, T2(b)–(e), T3) — the enumeration `decodeWeights`/`encodeWeights`, the generic
  `firstAccepted`, **`coherentMarketMaker`** with `coherentWeights`,
  `coherentMarketMaker_accepts/_coherent/_quote_eq_pi/_respects_true/_false`, the `smallSet`
  variant, **`interiorCoherentMarketMaker`** with `interiorWeights`, `interior_accepts`,
  `interior_fullSupport`, `interior_coherent`, **`interior_nonDogmatic`**,
  `interior_decided_at_truth`, `interior_D_ND_day`.
* **Sat** (T5) — **`pos_iff_satisfiable`** (+ `PCWorld` form, + at the interior maker).
* **Contrast** (T4(a)–(c)) — **`marketMaker_incoherent_on_pair`** (FAF's acceptance at `ε < 1`
  forces `quote φ + quote (∼φ) ≥ 2 − ε` on `T_pair`; `MarketMaker_pair_incoherent`,
  `marketMakerStates_pair_incoherent`), the N+ `coherent_pair_sum_one`, `coherent_pair_accepts`,
  `coherent_pair_not_marketMakerAccepts`, `interior_pair_quote_mem_Ioo`, `card_WD_empty`, and
  the responsive strategy `responsive_accepted_near_half`.
* **Recursion** (D5, T6) — `pcRec` (priced set `mentionedSet (firm n) ∪ X n`; record `X = ∅`,
  variant `X = smallSet`), `pcCoreState`, `pcCoreWeights`, `pcQuote`, `pcHistory`, `pcFirmStrat`,
  the day bound, **`pcOverlay_no_ec_trader_exploits`**, **`pcOverlay_coherent_mentioned`**,
  `pcOverlay_nonDogmatic`, `pcQuote_decided_true/false`, `D_PC_mentioned`, the assembly lemma
  (`ComputableMarket` assumed), `PCInductor` and `pcInductor`.
* **Witness** (T4(d), T6's witness) — the package over `paperDP 𝗜𝚺₁`.
* **Payoffs** (T8, extension) — Soto's intermediate payoffs as finite arithmetic (`variant`):
  `intermediateTotal_eq_completionProb`, `increments_telescope`, `bundle_total_decided`,
  `split_cash_inequality`.

No `sorry`; no OPEN statement in this attempt (T7 was not stated in Lean — see the attempt
report).
-/
