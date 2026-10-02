import Cleanroom.Bli.BliOverlay.AttemptB.Mentioned
import Cleanroom.Bli.BliOverlay.AttemptB.Subst
import Cleanroom.Bli.BliOverlay.AttemptB.Waived
import Cleanroom.Bli.BliOverlay.AttemptB.FirmSupport
import Cleanroom.Bli.BliOverlay.AttemptB.Recursion
import Cleanroom.Bli.BliOverlay.AttemptB.Witness
import Cleanroom.Bli.BliOverlay.AttemptB.WaivedRecursion
import Cleanroom.Bli.BliOverlay.AttemptB.Computation

/-!
# `bli-overlay`, attempt B: the overlay construction (Route O) through the past-view trader

Root module of attempt B (namespace `Cleanroom.Bli.BliOverlay.AttemptB`). The angle: the
overlaid recursion feeds FAF's `MarketMaker` the **past-substituted** firm strategy (every
day-`< n` price leaf replaced by the overlaid value) against the core past, so that the core
states are literally FAF's generic `marketMakerStates` of a trader (the past-view trader) and
`marketMaker_not_exploited` applies unchanged; a per-day exact value identity transfers the
conclusion to the firm on the overlaid market.

* **Mentioned** — D1 `mentionedSet` (= bli-found's `MentionedBy`), T1 value congruence on
  mentioned cells (real and rational, feature and strategy level).
* **Subst** — `EF.substPast` / `Strategy.substPast`, the substitution lemmas (value on `V` =
  value on the past view of `V`), `marketMakerAccepts_substPast_iff`, `MarketMaker_congr`.
* **Waived** — T3(a) the waived-days lemma `not_exploits_of_dayValue_le_off_finite`, T3(b) the
  acceptance bridge `dayValue_le_of_accepts` and the customer's entry point
  `dayValue_le_of_accepted_state` (+ `_subst`), T3(c) the firm corollary
  `no_ec_trader_exploits_of_firm_accepted_off_finite`.
* **FirmSupport** — T2 `firm_mentioned_small` (F2; `N₀ = (C+16)^2`), the structure
  `mentionedBy_TradingFirmAt_iff` (the firm's mentioned set is the union of the open enumerated
  traders', independent of `DP` and `Q`), the arithmetic `firmClock_arith`, the witness
  `firm_mentions_something`.
* **Recursion** — D2 `Overlay`, D3 the recursion `overlayDay` and its projections, the past-view
  trader, `coreState_eq_marketMakerStates`, T4 `overlay_firm_dayValue_le`,
  `overlay_firm_not_exploited`, **`overlay_no_ec_trader_exploits`** (L6(a)), the assembly lemma
  `overlay_isLogicalInductor_of_computableMarket` (market computability assumed), the sanity
  identity `overlayQuote_zero_eq_liaQuote`.
* **Witness** — T5 `overlay_half_ne_lia` over `paperDP 𝗜𝚺₁`.
* **WaivedRecursion** — T7 the waived recursion `waivedDay` (prescribed states on a finite `W`),
  `waived_no_ec_trader_exploits` through T3(c), the `W = ∅` cross-check `waived_empty_eq`.
* **Computation** — T6 (stretch) the bounded evaluator `overlayPrefixAtFuel` with `_mono_success`,
  `_sound`, `exists_`, the encoded day quote, the compiler boundary
  `OverlayBoundedEvaluatorCompiler` with `toComputableMarket` and
  `overlay_isLogicalInductor_of_compiler`; the boundary is **not instantiated** (OPEN).
-/
