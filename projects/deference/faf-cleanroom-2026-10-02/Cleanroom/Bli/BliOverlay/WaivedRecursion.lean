import Cleanroom.Bli.BliOverlay.Recursion
import Cleanroom.Bli.BliOverlay.AttemptA.WaivedRecursion

/-!
# `bli-overlay` · WaivedRecursion (reconciled): T7, the waived recursion

The same recursion as D3 except that on the days of a finite `W` the core state is a
prescribed finite table `pre n` (not searched), with the firm still built from the overlaid
past. Both attempts build it (attempt A by one `if n ∈ W` in the day step of the record's
recursion, attempt B likewise on its); both prove `waived_no_ec_trader_exploits` through T3
(on angle B the past-view trick covers only searched days, as the mandate notes — so T3(a) is
what carries the extension on both angles). The record takes attempt A's, which is the waived
form of the definition of record; its `W = ∅` instance is the record's recursion
(`waivedQuote_empty`, `waivedCoreState_empty`). Attempt B's waived recursion was not
cross-checked against this one (only the unwaived recursions were, `CrossCheck.lean`).

Sources: [[bli-overlay-mandate]] T7; [[bli-program]] §3.3 (iii), §3.6 (vi).
-/

namespace Cleanroom.Bli.BliOverlay

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

noncomputable section

/-- **T7 (of record). The waived recursion's core state**: `pre n` on `W`, the market maker's
output (against the firm built from the waived overlaid table and the restricted waived past)
off `W`.
Source: [[bli-overlay-mandate]] T7
Kind: D
Fidelity: exact -/
abbrev waivedCoreState (W : Finset ℕ) (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess)
    (ov : Overlay) (n : ℕ) : RationalBeliefState :=
  AttemptA.waivedCoreState W pre DP ov n

/-- The waived recursion's overlaid table.
Source: [[bli-overlay-mandate]] T7
Kind: D
Fidelity: exact -/
abbrev waivedQuote (W : Finset ℕ) (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess)
    (ov : Overlay) : ℕ → Sentence → ℚ :=
  AttemptA.waivedQuote W pre DP ov

/-- The waived recursion's market.
Source: [[bli-overlay-mandate]] T7
Kind: D
Fidelity: exact -/
abbrev waivedHistory (W : Finset ℕ) (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess)
    (ov : Overlay) : History :=
  AttemptA.waivedHistory W pre DP ov

/-- The waived recursion's day-`n` firm: the trading firm built from the waived overlaid table.
Source: [[bli-overlay-mandate]] T7
Kind: D
Fidelity: exact -/
abbrev waivedFirmStrat (W : Finset ℕ) (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess)
    (ov : Overlay) (n : ℕ) : Strategy n :=
  AttemptA.waivedFirmStrat W pre DP ov n

/-- The waived firm is the static firm on the waived table (the wrong-market guard for T7).
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
theorem waivedFirmStrat_eq (W : Finset ℕ) (pre : ℕ → RationalBeliefState)
    (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    waivedFirmStrat W pre DP ov n = TradingFirmAt DP (waivedQuote W pre DP ov) n := rfl

/-- On a waived day the core state is the prescribed table.
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
theorem waivedCoreState_of_mem (W : Finset ℕ) (pre : ℕ → RationalBeliefState)
    (DP : DeductiveProcess) (ov : Overlay) {n : ℕ} (hn : n ∈ W) :
    waivedCoreState W pre DP ov n = pre n :=
  AttemptA.waivedCoreState_of_mem W pre DP ov hn

/-- **T7, the day bound off `W`.**
Source: [[bli-overlay-mandate]] T7
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem waived_firm_dayValue_le (W : Finset ℕ) (pre : ℕ → RationalBeliefState)
    (DP : DeductiveProcess) (ov : Overlay) {n : ℕ} (hn : n ∉ W) :
    ∀ v : PCWorld, (waivedFirmStrat W pre DP ov n).value (waivedHistory W pre DP ov) v.payout ≤
      (marketMakerError n : ℝ) :=
  AttemptA.waived_firm_dayValue_le W pre DP ov hn

/-- **T7. The firm does not exploit the waived market**: T3(a) with this `W` — the waived part
of the waived-days lemma exercised by a construction.
Source: [[bli-overlay-mandate]] T7; [[bli-program]] §3.3 (iii)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem waived_firm_not_exploited (W : Finset ℕ) (pre : ℕ → RationalBeliefState)
    (DP : DeductiveProcess) (ov : Overlay) :
    ¬ (tradingFirmTrader DP (waivedQuote W pre DP ov)).Exploits (waivedHistory W pre DP ov) DP :=
  AttemptA.waived_firm_not_exploited W pre DP ov

/-- **T7 (headline). No efficiently computable trader exploits the waived overlaid market**, for
every finite `W`, every prescribed table `pre`, every process and every overlay.
Source: [[bli-overlay-mandate]] T7; [[bli-program]] §3.3 (iii), §3.6 (vi)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem waived_no_ec_trader_exploits (W : Finset ℕ) (pre : ℕ → RationalBeliefState)
    (DP : DeductiveProcess) (ov : Overlay) (Tr : Trader) (hTr : EfficientlyComputable Tr) :
    ¬ Tr.Exploits (waivedHistory W pre DP ov) DP :=
  AttemptA.waived_no_ec_trader_exploits W pre DP ov Tr hTr

/-! ## `W = ∅` is the unwaived recursion -/

/-- With `W = ∅` the waived table is `overlayQuote`: T4 is the `W = ∅` instance of T7.
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
theorem waivedQuote_empty (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess) (ov : Overlay) :
    waivedQuote ∅ pre DP ov = overlayQuote DP ov :=
  AttemptA.waivedQuote_empty pre DP ov

/-- With `W = ∅` the waived core states are the record's.
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
theorem waivedCoreState_empty (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess)
    (ov : Overlay) (n : ℕ) : waivedCoreState ∅ pre DP ov n = coreState DP ov n := by
  show (AttemptA.waivedRec ∅ pre DP ov n).core = (AttemptA.dayRec DP ov n).core
  rw [AttemptA.waivedRec_empty]

/-- With `W = ∅` the waived market is the overlaid market.
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
theorem waivedHistory_empty (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess)
    (ov : Overlay) : waivedHistory ∅ pre DP ov = overlayHistory DP ov := by
  funext n φ
  show ((waivedQuote ∅ pre DP ov n φ : ℚ) : ℝ) = ((overlayQuote DP ov n φ : ℚ) : ℝ)
  rw [waivedQuote_empty]

end

end Cleanroom.Bli.BliOverlay
