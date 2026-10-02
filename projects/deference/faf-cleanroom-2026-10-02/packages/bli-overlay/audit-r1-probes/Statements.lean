import Cleanroom.Bli.BliOverlay

/-!
# bli-overlay · audit r1 (fidelity) · probe: statement-level checks

Not imported by the library. Each `example` is a claim the ledger or report makes about a
*statement* (not a proof), checked by elaboration:

1. both attempts' T2 and T3(a) are literally the record's statements (ledger: "same statement");
2. the wrong-market guard is definitional: the recursion's firm is the static firm's day-`n`
   strategy on the overlaid table, and the past handed to `MarketMaker` reads the overlaid table
   at every mentioned past cell;
3. the headline `overlay_no_ec_trader_exploits` specialises, at the zero overlay, to FAF's own
   LIA no-exploitation statement (the sanity identity is load-bearing, not decorative);
4. the ledger's `676` is `(10 + 16)^2` *given* the structured constant at `C = 10`, which is a
   reading of bli-found's proof term (`refine ⟨10, _⟩`), not a Lean statement — the example
   shows what `firm_mentioned_small_from` yields once such an `hC` is supplied.
-/

namespace Cleanroom.Bli.BliOverlay.AuditR1

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Bli.BliOverlay

/-! ## 1. The attempts' statements are the record's -/

example : ∃ N₀, ∀ n ≥ N₀, ∀ (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ) (φ : Sentence),
    MentionedBy (TradingFirmAt DP Q n) φ → SmallOn n φ := AttemptA.firm_mentioned_small

example : ∃ N₀, ∀ n ≥ N₀, ∀ (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ) (φ : Sentence),
    MentionedBy (TradingFirmAt DP Q n) φ → SmallOn n φ := AttemptB.firm_mentioned_small

example (Tr : Trader) (P : History) (DP : DeductiveProcess)
    (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1) (W : Finset ℕ)
    (hacc : ∀ n ∉ W, ∀ v : PCWorld, (Tr.strat n).value P v.payout ≤ (marketMakerError n : ℝ)) :
    ¬ Tr.Exploits P DP := AttemptB.not_exploits_of_dayValue_le_off_finite Tr P DP hP W hacc

/-! ## 2. The wrong-market guard, by unfolding -/

example (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    firmStrat DP ov n = (tradingFirmTrader DP (overlayQuote DP ov)).strat n := rfl

example (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    overlayHistory DP ov n = fun φ => ((overlayQuote DP ov n φ : ℚ) : ℝ) := rfl

-- at a mentioned past cell, the candidate history the market maker checked is the market itself
example (DP : DeductiveProcess) (ov : Overlay) {n k : ℕ} (hk : k < n) {φ : Sentence}
    (hφ : MentionedBy (firmStrat DP ov n) φ) :
    (candidateRationalHistory (overlayRestrictedPast DP ov n) n (coreState DP ov n) k φ : ℝ) =
      overlayHistory DP ov k φ := by
  rw [candidateRationalHistory, Function.update_of_ne (Nat.ne_of_lt hk),
    rationalHistory_overlayRestrictedPast DP ov hk (mem_mentionedSet_iff.mpr hφ)]
  rfl

/-! ## 3. The headline specialises to FAF's LIA statement at the zero overlay -/

example (DP : DeductiveProcess) (Tr : Trader) (hTr : EfficientlyComputable Tr) :
    ¬ Tr.Exploits (liaHistory DP) DP := by
  rw [← overlayHistory_zero_eq_liaHistory]
  exact overlay_no_ec_trader_exploits DP Overlay.zero Tr hTr

/-! ## 4. The numeric day is conditional on the structured constant -/

example (hC : ∀ (ts : List ℕ) (φ : Sentence) (rest : List ℕ),
      parseStructuredPaperPrime ts = some (φ, rest) →
        tokenSize φ ≤ 2 ^ (10 * (ts.length - rest.length)) + 10) :
    ∀ n ≥ 676, ∀ (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ) (φ : Sentence),
      MentionedBy (TradingFirmAt DP Q n) φ → SmallOn n φ := by
  have h := firm_mentioned_small_from hC
  norm_num at h
  exact h

end Cleanroom.Bli.BliOverlay.AuditR1
