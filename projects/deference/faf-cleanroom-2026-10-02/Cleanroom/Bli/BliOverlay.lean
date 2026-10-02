import Cleanroom.Bli.BliOverlay.Mentioned
import Cleanroom.Bli.BliOverlay.FirmSupport
import Cleanroom.Bli.BliOverlay.Waived
import Cleanroom.Bli.BliOverlay.Recursion
import Cleanroom.Bli.BliOverlay.CrossCheck
import Cleanroom.Bli.BliOverlay.Witness
import Cleanroom.Bli.BliOverlay.WaivedRecursion
import Cleanroom.Bli.BliOverlay.Computation
import Cleanroom.Bli.BliOverlay.AttemptA
import Cleanroom.Bli.BliOverlay.AttemptB

/-!
# `bli-overlay`: the overlay construction (Route O) — reconciled package

Root module of the dual package `bli-overlay` (area `bli`, namespace `Cleanroom.Bli.BliOverlay`),
over `bli-found` (`MentionedBy`, `tokenSize`, `SmallOn`, `smallSet`, the bridge bounds) and FAF's
construction (`MarketMaker`, `TradingFirmAt`, `trading_firm_dominance`, `liaStates`). Two
independent attempts (`AttemptA/`, the restricted-past recursion; `AttemptB/`, the past-view
trader) both reached every core target sorry-free; this package states each target once over
the **definitions of record** — attempt A's recursion for D3, attempt B's constant for T2 — and
adds the cross-check that the two recursions are the same object.

* **Mentioned** (D1, T1) — `mentionedSet` (= bli-found's `MentionedBy`), the leaf and strategy
  value congruences; `mentionedSet_eq_attemptB`.
* **FirmSupport** (T2, F2) — **`firm_mentioned_small`** (headline; `N₀ = (C+16)^2`, attempt B's
  estimate, attempt A's independent proof at `2^10 + 4C + 32`), `firm_mentioned_small_from`,
  the finite-set and support corollaries, `mentionedSet_TradingFirmAt_eq` /
  `mentionedSet_TradingFirmAt_indep` (Known issue 5), the N+ `firm_mentions_something`.
* **Waived** (T3) — **`not_exploits_of_dayValue_le_off_finite`** (headline), the customer's entry
  point `dayValue_le_of_accepted_state` (arbitrary table; plus the split and past-substituted
  forms), `dayValue_le_of_accepts`, `no_ec_trader_exploits_of_firm_accepted_off_finite`.
* **Recursion** (D2, D3, T4; the construction-facing file) — `Overlay`, `coreState`,
  `overlayQuote`, `overlayHistory`, `corePast`, `firmStrat`, the D3 identities, `coreState_eq`
  (FAF's `MarketMaker` on the firm against the restricted overlaid past), `coreState_accepts`;
  **`overlay_no_ec_trader_exploits`** (headline, L6(a)), the day bound, the assembly lemma
  (`ComputableMarket` assumed), `MarketMaker_eq_of_eqOn_mentioned`, the sanity identity
  `overlayQuote_zero_eq_liaQuote`.
* **CrossCheck** — **`coreState_quote_eq_attemptB`**: the two attempts' recursions produce the
  same core states and tables; hence `coreState_eq_marketMakerStates` (the record's states are
  FAF's `marketMakerStates` of attempt B's past-view trader) and a second derivation of the
  firm's non-exploitation through `marketMaker_not_exploited`.
* **Witness** (T5) — `overlay_half_ne_lia` over `paperDP 𝗜𝚺₁`, the strong form
  `overlay_half_differs_from` (every process), `overlay_half_paperDP_no_ec_trader_exploits`.
* **WaivedRecursion** (T7) — `waivedCoreState`, `waivedQuote`, `waivedHistory`,
  **`waived_no_ec_trader_exploits`**, the `W = ∅` identities.
* **Computation** (T6, stretch) — the compiler boundary `OverlayBoundedEvaluatorCompiler` with
  `toComputableMarket` and `overlay_isLogicalInductor_of_compiler`; **not instantiated**
  (`partial: computability open`).

No `sorry` anywhere in the package (attempts included); no OPEN statement.
-/
