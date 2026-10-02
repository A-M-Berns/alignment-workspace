import Cleanroom.Bli.BliOverlay.AttemptA.Mentioned
import Cleanroom.Bli.BliOverlay.AttemptA.Waived
import Cleanroom.Bli.BliOverlay.AttemptA.FirmSupport
import Cleanroom.Bli.BliOverlay.AttemptA.Recursion
import Cleanroom.Bli.BliOverlay.AttemptA.Witness
import Cleanroom.Bli.BliOverlay.AttemptA.WaivedRecursion
import Cleanroom.Bli.BliOverlay.AttemptA.Computation

/-!
# `bli-overlay`, attempt A: the overlay construction (Route O) by the restricted-past recursion

Root module of attempt A of the dual package `bli-overlay` (area `bli`, namespace
`Cleanroom.Bli.BliOverlay.AttemptA`), over `bli-found` (`MentionedBy`, `tokenSize`, `SmallOn`,
`smallSet`, the bridge bounds) and FAF's construction (`MarketMaker`, `TradingFirmAt`,
`trading_firm_dominance`, `liaStates`). Angle A: on day `n` the firm is built from the overlaid
table of the days `< n`, and FAF's `MarketMaker` is run against it and the **restricted past** —
the overlaid values on the days `< n` at the sentences the day-`n` firm mentions.

* **Mentioned** (D1, T1) — `mentionedSet` with `mem_mentionedSet_iff`, `support_subset_mentionedSet`;
  the leaf congruence `EF.denoteWith_eq_of_eqOn_priceQueries` (real and rational) and the strategy
  congruences `Strategy.value_eq_of_eqOn_mentioned`, `Strategy.marketValueRat_eq_of_eqOn_mentioned`.
* **Waived** (T3) — `not_exploits_of_dayValue_le_off_finite` (the waived-days lemma, headline),
  `dayValue_le_of_accepted_state` (the customer's entry point: any accepted table),
  `dayValue_le_of_accepts` (the acceptance bridge), `firm_not_exploits_of_accepted_off_finite`,
  `no_ec_trader_exploits_of_firm_accepted_off_finite` (headline).
* **FirmSupport** (T2, F2) — the structure lemmas `mentionedBy_TradingFirmAt` /
  `mentionedBy_TradingFirmAt_of_enumerated` / `mentionedSet_TradingFirmAt_eq`, the size bound
  `tokenSize_le_of_mentionedBy_enumerated`, the clock estimate `eventually_firm_clock_le`
  (`N₀ = 2^10 + 4C + 32`), **`firm_mentioned_small`** (headline), `firm_mentionedSet_subset_smallSet`,
  `firm_support_subset_smallSet`, and the N+ `firm_mentions_something`.
* **Recursion** (D2, D3, T4) — `Overlay` (with `.zero`, `.half`), `restrictState`/`restrictedPast`,
  the recursion `dayRec` and its readings `coreState`, `overlayQuote`, `overlayHistory`, `corePast`,
  `firmStrat`; the identities `overlayQuote_of_mem`, `overlayQuote_of_not_mem`,
  `overlayHistory_range`, `overlayHistory_eq_quote_cast`, `firmStrat_eq`, `coreState_eq`,
  `coreState_accepts`; T4: `overlay_firm_dayValue_le`, `overlay_firm_not_exploited`,
  **`overlay_no_ec_trader_exploits`** (headline, L6(a)), the assembly lemma
  `overlay_isLogicalInductor_of_computableMarket` (`ComputableMarket` assumed; Kind L), and the
  sanity identity `overlayQuote_zero_eq_liaQuote` via `MarketMaker_eq_of_eqOn_mentioned`.
* **Witness** (T5) — `overlay_half_ne_lia`, `overlayHistory_half_ne_liaHistory`,
  `overlay_half_paperDP_no_ec_trader_exploits` with `overlay_half_paperDP_hworld`, and
  `firm_mentions_something_paperDP`, over `paperDP 𝗜𝚺₁`.

* **WaivedRecursion** (T7) — `waivedRec` (the core state is a prescribed table `pre n` on the
  days of a finite `W`, the market maker's output elsewhere), `waivedCoreState_of_mem`,
  `waivedCoreState_accepts`, `waived_firm_dayValue_le`, `waived_firm_not_exploited`,
  **`waived_no_ec_trader_exploits`**, and `waivedRec_empty` / `waivedQuote_empty` (with `W = ∅`
  it is `dayRec`: T4 is the `W = ∅` instance of T7).

* **Computation** (T6, stretch) — the bounded evaluator `overlayPrefixAtFuel` over an explicit
  stage table (finite day records `OvRecord`, the denoted table `recTable`, the computable-order
  restricted past `restrictedPastL`), with `_mono_success`, `_sound` (a success is the semantic
  prefix `overlayRecPrefix`) and `exists_`; the process composite `overlayPrefixAtFuelP`; the
  encoded quote evaluators `overlayEncodedQuoteAtFuel` / `overlayEncodedQuoteNatAtFuel` with
  soundness against `overlayEncodedQuote`; and the compiler boundary
  `OverlayBoundedEvaluatorCompiler` with `.toComputableMarket` and
  `overlay_isLogicalInductor_of_compiler`. **The boundary is not instantiated** (that is FAF's
  `LIACompiler.lean`-sized item, and where `ov`'s computability would enter), so nothing here
  proves `ComputableMarket (overlayHistory DP ov)`; the assembly lemma's row stays
  `partial: computability open`.

No `sorry` anywhere in the attempt; no OPEN statement.
-/
