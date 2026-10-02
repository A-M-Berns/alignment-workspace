import Cleanroom.Bli.BliOverlay.Mentioned
import Cleanroom.Bli.BliOverlay.Waived
import Cleanroom.Bli.BliOverlay.AttemptA.Recursion

/-!
# `bli-overlay` · Recursion (reconciled): D2 overlays, D3 the overlaid recursion, T4

**The construction-facing file** (plan §0.5). The definitions of record for D2 and D3 are
attempt A's — the **restricted-past recursion**: on day `n` the firm is built from the overlaid
table of the days `< n` (`firmStrat DP ov n = TradingFirmAt DP (overlayQuote DP ov) n`, by
definition), and FAF's `MarketMaker` is run on that very strategy against the *restricted
overlaid past* (for each `k < n`, the finite state listing `(φ, overlayQuote k φ)` for `φ` in
the day-`n` firm's mentioned set). Why this angle is of record, and not attempt B's
(`MarketMaker` on the past-substituted strategy against the core past): it hands FAF's fixed
point the firm's own strategy and a past carrying the overlaid values — the literal reading of
[[bli-program]] §3.3 (ii) "the acceptance checked against the overlaid values at the strategy's
past-day leaves" — with no local transformation of the strategy; both attempts have zero (c)
clauses, so the mandate's tie-break (fewer `(c)`, definitional stand-ins counted) does not
separate them, and this is the tie-break. Attempt B's recursion is proved to produce the same
core states and the same table (`CrossCheck.lean`), so its characterisation of the states as
FAF's `marketMakerStates` of a trader transports to the record.

Sources: [[bli-overlay-mandate]] D2, D3, T4, §Attempt angles; [[bli-program]] §3.3.
-/

namespace Cleanroom.Bli.BliOverlay

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

noncomputable section

/-! ## D2: overlays -/

/-- **D2 (of record). An overlay**: the price written on an unmentioned sentence on day `n`, as
a function of the day, the days-`< n` core states, the day-`n` core state and the sentence —
finite data. The `[0,1]` range is a field, not a clamp.
Source: [[bli-overlay-mandate]] D2; [[bli-program]] §3.3 (ii)
Kind: D
Fidelity: exact -/
abbrev Overlay := AttemptA.Overlay

/-- The zero overlay: every unmentioned sentence is priced `0`, as FAF's LIA does.
Source: [[bli-overlay-mandate]] T4(v)
Kind: D
Fidelity: exact -/
abbrev Overlay.zero : Overlay := AttemptA.Overlay.zero

/-- The constant-`1/2` overlay of the witness T5.
Source: [[bli-overlay-mandate]] T5
Kind: D
Fidelity: exact -/
abbrev Overlay.half : Overlay := AttemptA.Overlay.half

/-! ## D3: the overlaid recursion (restricted past) -/

/-- **D3 (of record). The core state** of day `n`: FAF's `MarketMaker` run on the firm built
from the overlaid table, against the restricted overlaid past (`coreState_eq`).
Source: [[bli-overlay-mandate]] D3; [[bli-program]] §3.3 (ii)
Kind: D
Fidelity: exact -/
abbrev coreState (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) : RationalBeliefState :=
  AttemptA.coreState DP ov n

/-- **D3 (of record). The overlaid table**: the core quote on the day's mentioned set, the
overlay elsewhere (`overlayQuote_of_mem`, `overlayQuote_of_not_mem`).
Source: [[bli-overlay-mandate]] D3
Kind: D
Fidelity: exact -/
abbrev overlayQuote (DP : DeductiveProcess) (ov : Overlay) : ℕ → Sentence → ℚ :=
  AttemptA.overlayQuote DP ov

/-- **D3 (of record). The overlaid market**: the real history obtained by casting
`overlayQuote`.
Source: [[bli-overlay-mandate]] D3
Kind: D
Fidelity: exact -/
abbrev overlayHistory (DP : DeductiveProcess) (ov : Overlay) : History :=
  AttemptA.overlayHistory DP ov

/-- The list of the days-`< n` core states (the overlay's second argument).
Source: [[bli-overlay-mandate]] D3
Kind: D
Fidelity: exact -/
abbrev corePast (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) : List RationalBeliefState :=
  AttemptA.corePast DP ov n

/-- **D3 (of record). The firm's day-`n` strategy**: the trading firm built from the overlaid
table — by definition the day-`n` strategy of the static firm
`tradingFirmTrader DP (overlayQuote DP ov)` (`firmStrat_eq`).
Source: [[bli-overlay-mandate]] D3
Kind: D
Fidelity: exact -/
abbrev firmStrat (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) : Strategy n :=
  AttemptA.firmStrat DP ov n

/-- The restricted overlaid past fed to `MarketMaker` on day `n`: for each `k < n`, the finite
state with entries `(φ, overlayQuote DP ov k φ)` for `φ ∈ mentionedSet (firmStrat DP ov n)`.
Source: [[bli-overlay-mandate]] §Attempt angles (A)
Kind: D
Fidelity: exact -/
abbrev overlayRestrictedPast (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    List RationalBeliefState :=
  AttemptA.overlayRestrictedPast DP ov n

/-! ## The identities of D3 -/

/-- The overlaid quote, as a case split on the mentioned set.
Source: [[bli-overlay-mandate]] D3
Kind: L
Fidelity: exact -/
theorem overlayQuote_eq_ite (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) (φ : Sentence) :
    overlayQuote DP ov n φ =
      if φ ∈ mentionedSet (firmStrat DP ov n) then (coreState DP ov n).quote φ
      else ov.val n (corePast DP ov n) (coreState DP ov n) φ :=
  AttemptA.overlayQuote_eq_ite DP ov n φ

/-- **`overlayQuote_of_mem`**: on the mentioned set, the overlaid quote is the core quote.
Source: [[bli-overlay-mandate]] D3
Kind: L
Fidelity: exact -/
theorem overlayQuote_of_mem (DP : DeductiveProcess) (ov : Overlay) {n : ℕ} {φ : Sentence}
    (h : φ ∈ mentionedSet (firmStrat DP ov n)) :
    overlayQuote DP ov n φ = (coreState DP ov n).quote φ :=
  AttemptA.overlayQuote_of_mem DP ov h

/-- **`overlayQuote_of_not_mem`**: off the mentioned set, the overlaid quote is the overlay.
Source: [[bli-overlay-mandate]] D3
Kind: L
Fidelity: exact -/
theorem overlayQuote_of_not_mem (DP : DeductiveProcess) (ov : Overlay) {n : ℕ} {φ : Sentence}
    (h : φ ∉ mentionedSet (firmStrat DP ov n)) :
    overlayQuote DP ov n φ = ov.val n (corePast DP ov n) (coreState DP ov n) φ :=
  AttemptA.overlayQuote_of_not_mem DP ov h

/-- `overlayQuote` is in `[0,1]` (`RationalBeliefState.bounded` on the mentioned set,
`Overlay.range` off it; no clamp).
Source: [[bli-overlay-mandate]] D3
Kind: L
Fidelity: exact -/
theorem overlayQuote_range (DP : DeductiveProcess) (ov : Overlay) :
    ∀ k φ, 0 ≤ overlayQuote DP ov k φ ∧ overlayQuote DP ov k φ ≤ 1 :=
  AttemptA.overlayQuote_range DP ov

/-- **`overlayHistory_range`**: the `def:market` range clause for the overlaid market.
Source: [[bli-overlay-mandate]] D3
Kind: L
Fidelity: exact -/
theorem overlayHistory_range (DP : DeductiveProcess) (ov : Overlay) :
    ∀ day φ, 0 ≤ overlayHistory DP ov day φ ∧ overlayHistory DP ov day φ ≤ 1 :=
  AttemptA.overlayHistory_range DP ov

/-- **`overlayHistory_eq_quote_cast`**: the real market is the cast of the exact rational table.
Source: [[bli-overlay-mandate]] D3
Kind: L
Fidelity: exact -/
theorem overlayHistory_eq_quote_cast (DP : DeductiveProcess) (ov : Overlay) (day : ℕ)
    (φ : Sentence) : overlayHistory DP ov day φ = (overlayQuote DP ov day φ : ℝ) := rfl

/-- **`firmStrat_eq`** (the wrong-market guard): the recursion's firm strategy is the day-`n`
strategy of the static complete-table firm on the overlaid table — the trader
`trading_firm_dominance` quantifies over.
Source: [[bli-overlay-mandate]] D3; [[bli-program]] §7 item 3
Kind: L
Fidelity: exact -/
theorem firmStrat_eq (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    firmStrat DP ov n = (tradingFirmTrader DP (overlayQuote DP ov)).strat n := rfl

/-- `firmStrat` unfolded: the firm built from the whole overlaid table (it reads days `< n`).
Source: [[bli-overlay-mandate]] D3
Kind: L
Fidelity: exact -/
theorem firmStrat_eq_TradingFirmAt (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    firmStrat DP ov n = TradingFirmAt DP (overlayQuote DP ov) n := rfl

/-- On days `< n` and mentioned sentences, the restricted overlaid past reads the overlaid
table — the fact an auditor unfolding `overlayQuote` at a past-day leaf finds.
Source: [[bli-overlay-mandate]] T4 trap (i)
Kind: L
Fidelity: exact -/
theorem rationalHistory_overlayRestrictedPast (DP : DeductiveProcess) (ov : Overlay) {n k : ℕ}
    (hk : k < n) {φ : Sentence} (hφ : φ ∈ mentionedSet (firmStrat DP ov n)) :
    rationalHistory (overlayRestrictedPast DP ov n) k φ = overlayQuote DP ov k φ :=
  AttemptA.rationalHistory_restrictedPast hk hφ

/-- **`coreState_eq`**: the day-`n` core state is FAF's `MarketMaker` on `firmStrat n` against
the restricted overlaid past.
Source: [[bli-overlay-mandate]] D3, §Attempt angles (A)
Kind: L
Fidelity: exact -/
theorem coreState_eq (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    coreState DP ov n = MarketMaker (firmStrat DP ov n) (overlayRestrictedPast DP ov n)
      (marketMakerError n) (marketMakerError_pos n) :=
  AttemptA.coreState_eq DP ov n

/-- **The core state is accepted** by the market maker against `firmStrat n` and the restricted
overlaid past (FAF's `MarketMaker_accepts`, applied).
Source: [[bli-overlay-mandate]] T4
Kind: L
Fidelity: exact -/
theorem coreState_accepts (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    MarketMakerAccepts (firmStrat DP ov n) (overlayRestrictedPast DP ov n) (marketMakerError n)
      (coreState DP ov n) :=
  AttemptA.coreState_accepts DP ov n

/-! ## T4: the overlaid recursion is exploited by no e.c. trader -/

/-- **T4, the day bound.** The firm's day-`n` strategy — built from and evaluated on the
**overlaid** history — has value at most `marketMakerError n` in every p.c. world: the core
state is accepted against the restricted overlaid past, and that candidate history agrees with
the overlaid history on every mentioned cell (days `< n` by the restriction, day `n` because
the overlaid quote is the core quote on the mentioned set), so T3(b) applies.
Source: [[bli-overlay-mandate]] T4; [[bli-program]] §3.3 (i)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem overlay_firm_dayValue_le (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    ∀ v : PCWorld,
      (firmStrat DP ov n).value (overlayHistory DP ov) v.payout ≤ (marketMakerError n : ℝ) :=
  AttemptA.overlay_firm_dayValue_le DP ov n

/-- **T4. The firm does not exploit the overlaid market**: T3(a) with `W = ∅`.
Source: [[bli-overlay-mandate]] T4; [[bli-program]] §3.3 (iii)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem overlay_firm_not_exploited (DP : DeductiveProcess) (ov : Overlay) :
    ¬ (tradingFirmTrader DP (overlayQuote DP ov)).Exploits (overlayHistory DP ov) DP :=
  AttemptA.overlay_firm_not_exploited DP ov

/-- **T4 (L6(a), headline, load-bearing). No efficiently computable trader exploits the
overlaid market**, for every process `DP` and every overlay `ov`: by FAF's
`trading_firm_dominance` an exploiting e.c. trader would make the static firm on the overlaid
table exploit it, and the firm does not (`overlay_firm_not_exploited`). Both attempts prove
this; attempt B's route (`marketMaker_not_exploited` on the past-view trader, transported by an
exact value identity) reaches the same statement over its recursion, which `CrossCheck.lean`
identifies with this one.
Source: [[bli-overlay-mandate]] T4; [[bli-program]] §3.3, §4 row L6(a)
Kind: C
Fidelity: exact
Hyps: (a) — `MarketMaker_accepts`, `trading_firm_dominance` are FAF theorems, applied;
`ov.range` is a field of D2 -/
theorem overlay_no_ec_trader_exploits (DP : DeductiveProcess) (ov : Overlay) (Tr : Trader)
    (hTr : EfficientlyComputable Tr) : ¬ Tr.Exploits (overlayHistory DP ov) DP :=
  AttemptA.overlay_no_ec_trader_exploits DP ov Tr hTr

/-- **Assembly lemma (Kind L).** The overlaid market is a logical inductor **if** it is a
computable market — the computability is *assumed*, as in FAF's
`lia_isLogicalInductor_of_computableMarket`; nothing in this package establishes it (T6's
compiler boundary is not instantiated). Ledger row: `partial: computability open`.
Source: [[bli-overlay-mandate]] T4 (assembly); [[bli-program]] §7 item 8
Kind: L
Fidelity: weaker: `ComputableMarket (overlayHistory DP ov)` is a hypothesis, not proved
Hyps: (b) `hmarket : ComputableMarket (overlayHistory DP ov)` — assumed (L6(b), open);
(a) `hDP` is the process's computability, the criterion's own hypothesis -/
theorem overlay_isLogicalInductor_of_computableMarket (DP : DeductiveProcess) (ov : Overlay)
    (hDP : ComputableDeductiveProcess DP) (hmarket : ComputableMarket (overlayHistory DP ov)) :
    IsLogicalInductor (overlayHistory DP ov) DP :=
  AttemptA.overlay_isLogicalInductor_of_computableMarket DP ov hDP hmarket

/-! ## The sanity identity: the zero overlay is FAF's LIA -/

/-- **`MarketMaker` congruence on mentioned cells.** Two pasts that agree, on every day `< n`,
at every sentence the strategy mentions, give the same market-maker output (the acceptance
predicate is the same for every candidate, so the `Nat.find` is the same). Attempt B's
`MarketMaker_congr` is the engine in predicate form.
Source: [[bli-overlay-mandate]] T4(v)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem MarketMaker_eq_of_eqOn_mentioned {n : ℕ} (T : Strategy n)
    (past₁ past₂ : List RationalBeliefState) (ε : ℚ) (hε : 0 < ε)
    (h : ∀ φ, MentionedBy T φ → ∀ k < n, rationalHistory past₁ k φ = rationalHistory past₂ k φ) :
    MarketMaker T past₁ ε hε = MarketMaker T past₂ ε hε :=
  AttemptA.MarketMaker_eq_of_eqOn_mentioned T past₁ past₂ ε hε h

/-- **T4(v). The zero overlay is FAF's LIA**: `overlayQuote DP Overlay.zero = liaQuote DP`. The
artifact check that D3 is the right object and not a relabelling: with `ov = 0` the core states
are `liaStates` and off the mentioned set both tables quote `0` (the LIA state's support is
inside the firm's support, which is inside the mentioned set). Both attempts prove it.
Source: [[bli-overlay-mandate]] T4(v)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem overlayQuote_zero_eq_liaQuote (DP : DeductiveProcess) :
    overlayQuote DP Overlay.zero = liaQuote DP :=
  AttemptA.overlayQuote_zero_eq_liaQuote DP

/-- With the zero overlay, the overlaid market is `liaHistory`.
Source: [[bli-overlay-mandate]] T4(v)
Kind: L
Fidelity: exact -/
theorem overlayHistory_zero_eq_liaHistory (DP : DeductiveProcess) :
    overlayHistory DP Overlay.zero = liaHistory DP :=
  AttemptA.overlayHistory_zero_eq_liaHistory DP

end

end Cleanroom.Bli.BliOverlay
