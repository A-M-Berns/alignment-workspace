import Cleanroom.Bli.BliOverlay.Recursion
import Cleanroom.Bli.BliOverlay.AttemptB.Recursion

/-!
# `bli-overlay` · CrossCheck: the two attempts' recursions coincide

The mandate (§Attempt angles) asks the reconciler to cross-check that the two recursions
produce the same core states — "they should: `MarketMaker` depends on its inputs only through
the mentioned cells". They do, and this file proves it: for every process, every overlay and
every day, attempt A's restricted-past recursion (the definition of record) and attempt B's
past-view recursion return **the same core state and the same overlaid table**
(`coreState_quote_eq_attemptB`, by strong induction on the day). The day step is the
`MarketMaker` congruence `AttemptB.MarketMaker_congr`: acceptance of the bare firm against the
restricted overlaid past is the same predicate as acceptance of the past-substituted firm
against the core past, because the substituted strategy's value on any candidate history reads
the substituted constants — the overlaid values — at every past cell it mentions, and the
restricted past lists exactly those values (`rationalHistory_overlayRestrictedPast`).

What the identity buys: attempt B's characterisation of the states as FAF's generic
`marketMakerStates` of a trader transports to the record (`coreState_eq_marketMakerStates`),
so the package holds both readings of the same object — FAF's `MarketMaker` on the firm against
the overlaid past (by definition), and FAF's market-maker recursion for the past-view trader
(by theorem) — and every theorem of attempt B about its recursion is a theorem about the
record's (`overlayQuote_eq_attemptB`, `overlayHistory_eq_attemptB`).

Sources: [[bli-overlay-mandate]] §Attempt angles; [[bli-overlay-report]] §Two attempts.
-/

namespace Cleanroom.Bli.BliOverlay

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

noncomputable section

/-- An overlay of record, read as attempt B's overlay (the same two fields).
Source: reconciliation (D2)
Kind: D
Fidelity: exact -/
def Overlay.toB (ov : Overlay) : AttemptB.Overlay := ⟨ov.val, ov.range⟩

/-- `Overlay.toB` keeps the value function.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem Overlay.toB_val (ov : Overlay) : ov.toB.val = ov.val := rfl

/-- The half overlay reads as attempt B's half overlay.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Overlay.half_toB : Overlay.half.toB = AttemptB.Overlay.half := rfl

/-- The zero overlay reads as attempt B's zero overlay.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Overlay.zero_toB : Overlay.zero.toB = AttemptB.Overlay.zero := rfl

/-- **The cross-check.** For every process, overlay and day, the record's (attempt A's,
restricted-past) recursion and attempt B's (past-view) recursion produce the same core state
and the same overlaid day table. Strong induction on the day: the firms coincide (both read the
overlaid table below `n`, equal by the induction hypothesis), the mentioned sets coincide, the
core pasts coincide, and the market makers coincide by `AttemptB.MarketMaker_congr` — the bare
firm against the restricted overlaid past accepts exactly the candidates the past-substituted
firm against the core past accepts (same support by `Strategy.support_substPast`; same exact
value on every candidate history by `Strategy.marketValueRat_substPast` and T1, since at every
mentioned past cell the substituted constant is the overlaid value the restricted past lists,
and on day `n` both read the candidate). The quotes then agree cell by cell.
Source: [[bli-overlay-mandate]] §Attempt angles (the reconciler's cross-check)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem coreState_quote_eq_attemptB (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    coreState DP ov n = AttemptB.coreState DP ov.toB n ∧
      ∀ φ, overlayQuote DP ov n φ = AttemptB.overlayQuote DP ov.toB n φ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    -- the day-`n` firms coincide: both are built from the overlaid table below `n`
    have hfirm : firmStrat DP ov n = AttemptB.firmStrat DP ov.toB n := by
      show TradingFirmAt DP (overlayQuote DP ov) n =
        TradingFirmAt DP (AttemptB.quoteBelow DP ov.toB n) n
      apply TradingFirmAt_eq_of_eq_prefix
      intro k hk φ
      rw [AttemptB.quoteBelow_of_lt DP ov.toB hk φ]
      exact (ih k hk).2 φ
    -- hence the mentioned sets coincide
    have hms : mentionedSet (firmStrat DP ov n) =
        AttemptB.mentionedSet (AttemptB.firmStrat DP ov.toB n) := by
      rw [mentionedSet_eq_attemptB, hfirm]
    -- and the core pasts coincide (induction hypothesis on the states)
    have hpast : corePast DP ov n = AttemptB.corePast DP ov.toB n := by
      show (List.ofFn fun i : Fin n => coreState DP ov i) =
        List.ofFn fun i : Fin n => AttemptB.coreState DP ov.toB i
      congr 1
      funext i
      exact (ih i i.isLt).1
    -- the support of the past-substituted firm is the firm's
    have hs : (AttemptB.pvStrat DP ov.toB n).support = (firmStrat DP ov n).support := by
      unfold AttemptB.pvStrat
      rw [AttemptB.Strategy.support_substPast, hfirm]
    -- the exact values on the two candidate histories agree, for every candidate `B`
    have hval : ∀ (B : RationalBeliefState) (w : Sentence → ℚ),
        (AttemptB.pvStrat DP ov.toB n).marketValueRat
            (candidateRationalHistory (AttemptB.corePast DP ov.toB n) n B) w =
          (firmStrat DP ov n).marketValueRat
            (candidateRationalHistory (overlayRestrictedPast DP ov n) n B) w := by
      intro B w
      unfold AttemptB.pvStrat
      rw [AttemptB.Strategy.marketValueRat_substPast, ← hfirm]
      apply Strategy.marketValueRat_eq_of_eqOn_mentioned
      intro φ hφ k hk
      rcases Nat.lt_or_eq_of_le hk with hlt | rfl
      · rw [AttemptB.EF.pastViewRat_of_lt hlt, AttemptB.quoteBelow_of_lt DP ov.toB hlt,
          ← (ih k hlt).2 φ]
        simp only [candidateRationalHistory, Function.update_of_ne (Nat.ne_of_lt hlt)]
        rw [rationalHistory_overlayRestrictedPast DP ov hlt (mem_mentionedSet_iff.mpr hφ)]
      · rw [AttemptB.EF.pastViewRat_self]
        simp [candidateRationalHistory]
    -- the core states coincide: `MarketMaker` congruence
    have hcore : coreState DP ov n = AttemptB.coreState DP ov.toB n := by
      rw [coreState_eq, AttemptB.coreState_eq]
      apply AttemptB.MarketMaker_congr
      intro B
      constructor
      · intro h
        exact AttemptB.MarketMakerAccepts.of_support_eq hs (hval B) h
      · intro h
        exact AttemptB.MarketMakerAccepts.of_support_eq hs.symm (fun w => (hval B w).symm) h
    refine ⟨hcore, fun φ => ?_⟩
    rw [overlayQuote_eq_ite, AttemptB.overlayQuote_eq]
    simp only [hms, hcore, hpast, Overlay.toB_val]

/-- **The core states coincide** (the cross-check, states only).
Source: [[bli-overlay-mandate]] §Attempt angles
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem coreState_eq_attemptB (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    coreState DP ov n = AttemptB.coreState DP ov.toB n :=
  (coreState_quote_eq_attemptB DP ov n).1

/-- **The overlaid tables coincide** (the cross-check, tables).
Source: [[bli-overlay-mandate]] §Attempt angles
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem overlayQuote_eq_attemptB (DP : DeductiveProcess) (ov : Overlay) :
    overlayQuote DP ov = AttemptB.overlayQuote DP ov.toB := by
  funext n φ
  exact (coreState_quote_eq_attemptB DP ov n).2 φ

/-- **The overlaid markets coincide.**
Source: [[bli-overlay-mandate]] §Attempt angles
Kind: L
Fidelity: exact -/
theorem overlayHistory_eq_attemptB (DP : DeductiveProcess) (ov : Overlay) :
    overlayHistory DP ov = AttemptB.overlayHistory DP ov.toB := by
  funext n φ
  show ((overlayQuote DP ov n φ : ℚ) : ℝ) = ((AttemptB.overlayQuote DP ov.toB n φ : ℚ) : ℝ)
  rw [overlayQuote_eq_attemptB]

/-- The day-`n` firms coincide.
Source: [[bli-overlay-mandate]] §Attempt angles
Kind: L
Fidelity: exact -/
theorem firmStrat_eq_attemptB (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    firmStrat DP ov n = AttemptB.firmStrat DP ov.toB n := by
  rw [AttemptB.firmStrat_eq, firmStrat_eq_TradingFirmAt, overlayQuote_eq_attemptB]

/-! ## Attempt B's characterisation, transported to the record -/

/-- **The record's core states are FAF's `marketMakerStates` of attempt B's past-view trader**
(`AttemptB.pvTrader`: on day `n` it plays the firm's day-`n` strategy with every day-`< n`
price leaf replaced by the overlaid value). This is angle B's signature identity, made a
theorem about the definition of record through the cross-check: the restricted-past recursion
*is* FAF's generic market-maker recursion for that trader.
Source: [[bli-overlay-mandate]] §Attempt angles (B); reconciliation
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem coreState_eq_marketMakerStates (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    coreState DP ov n = marketMakerStates (AttemptB.pvTrader DP ov.toB) n := by
  rw [coreState_eq_attemptB]
  exact AttemptB.coreState_eq_marketMakerStates DP ov.toB n

/-- **T4 by attempt B's route, on the record's recursion**: the firm on the overlaid table does
not exploit the overlaid market, obtained from FAF's `marketMaker_not_exploited` for the
past-view trader transported along the equality of plausible-assessment sets (attempt B's
`overlay_firm_not_exploited`) and the cross-check — an independent second derivation of
`overlay_firm_not_exploited` (which goes through T3(a) with `W = ∅`).
Source: [[bli-overlay-mandate]] T4, §Attempt angles (B)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem overlay_firm_not_exploited_via_marketMaker (DP : DeductiveProcess) (ov : Overlay) :
    ¬ (tradingFirmTrader DP (overlayQuote DP ov)).Exploits (overlayHistory DP ov) DP := by
  rw [overlayQuote_eq_attemptB, overlayHistory_eq_attemptB]
  exact AttemptB.overlay_firm_not_exploited DP ov.toB

end

end Cleanroom.Bli.BliOverlay
