import Cleanroom.Bli.BliOverlay.AttemptB.Recursion

/-!
# `bli-overlay` (attempt B) · WaivedRecursion: the waived recursion (T7)

The same recursion as `Recursion.lean`, except that on the days of a finite set `W` the core
state is a **prescribed** finite table `pre n` (not searched), with the firm still built from the
overlaid past and the overlay still set off the firm's mentioned set. On angle B the past-view
trick covers only the searched days, so the no-exploitation goes through T3: on every day
`n ∉ W` the core state is accepted for the past-substituted firm against the core past
(`waivedCore_accepts`), hence the day bound on the overlaid history
(`dayValue_le_of_accepted_state_subst`), hence `waived_no_ec_trader_exploits` by T3(c).

`waived_empty_eq` is the cross-check: with `W = ∅` the waived recursion is the plain overlaid
recursion (core states and quotes), by the same strong induction. This is the shape
`bli-exact-base` K7 (the finite-segment splice) and B3's initial segments need.
-/

namespace Cleanroom.Bli.BliOverlay.AttemptB

open LogicalInduction Cleanroom.Bli.BliFound

/-! ## D3 with waived days -/

/-- **T7. One day of the waived recursion**: as `overlayDay`, but on a day `n ∈ W` the core state
is the prescribed `pre n` instead of the market maker's search.
Source: [[bli-overlay-mandate]] T7; [[bli-program]] §3.3 (iii), §3.6 (vi)
Kind: D
Fidelity: exact -/
noncomputable def waivedDay (DP : DeductiveProcess) (ov : Overlay) (W : Finset ℕ)
    (pre : ℕ → RationalBeliefState) : ℕ → RationalBeliefState × (Sentence → ℚ)
  | n =>
      let past : List RationalBeliefState := List.ofFn fun i : Fin n => (waivedDay DP ov W pre i).1
      let below : ℕ → Sentence → ℚ :=
        fun k φ => if _h : k < n then (waivedDay DP ov W pre k).2 φ else 0
      let firm : Strategy n := TradingFirmAt DP below n
      let B : RationalBeliefState :=
        if n ∈ W then pre n
        else MarketMaker (Strategy.substPast below firm) past (marketMakerError n)
          (marketMakerError_pos n)
      (B, fun φ => if φ ∈ mentionedSet firm then B.quote φ else ov.val n past B φ)
termination_by n => n
decreasing_by
  all_goals first | exact i.isLt | exact _h

/-- The day-`n` core state of the waived recursion.
Source: [[bli-overlay-mandate]] T7
Kind: D
Fidelity: exact -/
noncomputable def waivedCore (DP : DeductiveProcess) (ov : Overlay) (W : Finset ℕ)
    (pre : ℕ → RationalBeliefState) (n : ℕ) : RationalBeliefState :=
  (waivedDay DP ov W pre n).1

/-- The waived recursion's overlaid quote table.
Source: [[bli-overlay-mandate]] T7
Kind: D
Fidelity: exact -/
noncomputable def waivedQuote (DP : DeductiveProcess) (ov : Overlay) (W : Finset ℕ)
    (pre : ℕ → RationalBeliefState) : ℕ → Sentence → ℚ :=
  fun n φ => (waivedDay DP ov W pre n).2 φ

/-- The waived recursion's core past.
Source: [[bli-overlay-mandate]] T7
Kind: D
Fidelity: exact -/
noncomputable def waivedPast (DP : DeductiveProcess) (ov : Overlay) (W : Finset ℕ)
    (pre : ℕ → RationalBeliefState) (n : ℕ) : List RationalBeliefState :=
  List.ofFn fun i : Fin n => waivedCore DP ov W pre i

/-- The waived recursion's overlaid table below `n`.
Source: [[bli-overlay-mandate]] T7
Kind: D
Fidelity: exact -/
noncomputable def waivedBelow (DP : DeductiveProcess) (ov : Overlay) (W : Finset ℕ)
    (pre : ℕ → RationalBeliefState) (n : ℕ) : ℕ → Sentence → ℚ :=
  fun k φ => if k < n then waivedQuote DP ov W pre k φ else 0

/-- The waived recursion's firm strategy on day `n`, built from the overlaid table below `n`.
Source: [[bli-overlay-mandate]] T7
Kind: D
Fidelity: exact -/
noncomputable def waivedFirm (DP : DeductiveProcess) (ov : Overlay) (W : Finset ℕ)
    (pre : ℕ → RationalBeliefState) (n : ℕ) : Strategy n :=
  TradingFirmAt DP (waivedBelow DP ov W pre n) n

/-- The waived recursion's past-view strategy on day `n`.
Source: [[bli-overlay-mandate]] T7
Kind: D
Fidelity: exact -/
noncomputable def waivedPv (DP : DeductiveProcess) (ov : Overlay) (W : Finset ℕ)
    (pre : ℕ → RationalBeliefState) (n : ℕ) : Strategy n :=
  Strategy.substPast (waivedBelow DP ov W pre n) (waivedFirm DP ov W pre n)

/-- The waived recursion's real market.
Source: [[bli-overlay-mandate]] T7
Kind: D
Fidelity: exact -/
noncomputable def waivedHistory (DP : DeductiveProcess) (ov : Overlay) (W : Finset ℕ)
    (pre : ℕ → RationalBeliefState) : History :=
  fun n φ => (waivedQuote DP ov W pre n φ : ℝ)

/-- The day-`n` core state as the recursion chooses it: prescribed on `W`, searched off `W`.
Source: [[bli-overlay-mandate]] T7
Kind: D
Fidelity: exact -/
noncomputable def waivedChoice (DP : DeductiveProcess) (ov : Overlay) (W : Finset ℕ)
    (pre : ℕ → RationalBeliefState) (n : ℕ) : RationalBeliefState :=
  if n ∈ W then pre n
  else MarketMaker (waivedPv DP ov W pre n) (waivedPast DP ov W pre n) (marketMakerError n)
    (marketMakerError_pos n)

/-- The one-step unfolding of the waived recursion.
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
lemma waivedDay_eq (DP : DeductiveProcess) (ov : Overlay) (W : Finset ℕ)
    (pre : ℕ → RationalBeliefState) (n : ℕ) :
    waivedDay DP ov W pre n =
      (waivedChoice DP ov W pre n,
       fun φ => if φ ∈ mentionedSet (waivedFirm DP ov W pre n) then
          (waivedChoice DP ov W pre n).quote φ
        else ov.val n (waivedPast DP ov W pre n) (waivedChoice DP ov W pre n) φ) := by
  rw [waivedDay]
  rfl

/-- The core state is the recursion's choice.
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
lemma waivedCore_eq (DP : DeductiveProcess) (ov : Overlay) (W : Finset ℕ)
    (pre : ℕ → RationalBeliefState) (n : ℕ) :
    waivedCore DP ov W pre n = waivedChoice DP ov W pre n := by
  unfold waivedCore
  rw [waivedDay_eq]

/-- On a waived day the core state is the prescribed table.
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
lemma waivedCore_of_mem (DP : DeductiveProcess) (ov : Overlay) (W : Finset ℕ)
    (pre : ℕ → RationalBeliefState) {n : ℕ} (hn : n ∈ W) :
    waivedCore DP ov W pre n = pre n := by
  rw [waivedCore_eq]
  unfold waivedChoice
  rw [if_pos hn]

/-- On a searched day the core state is the market maker's fixed point against the past-view
strategy on the core past.
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
lemma waivedCore_of_not_mem (DP : DeductiveProcess) (ov : Overlay) (W : Finset ℕ)
    (pre : ℕ → RationalBeliefState) {n : ℕ} (hn : n ∉ W) :
    waivedCore DP ov W pre n =
      MarketMaker (waivedPv DP ov W pre n) (waivedPast DP ov W pre n) (marketMakerError n)
        (marketMakerError_pos n) := by
  rw [waivedCore_eq]
  unfold waivedChoice
  rw [if_neg hn]

/-- The waived quote, unfolded.
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
lemma waivedQuote_eq (DP : DeductiveProcess) (ov : Overlay) (W : Finset ℕ)
    (pre : ℕ → RationalBeliefState) (n : ℕ) (φ : Sentence) :
    waivedQuote DP ov W pre n φ =
      if φ ∈ mentionedSet (waivedFirm DP ov W pre n) then (waivedCore DP ov W pre n).quote φ
      else ov.val n (waivedPast DP ov W pre n) (waivedCore DP ov W pre n) φ := by
  unfold waivedQuote
  rw [waivedDay_eq, waivedCore_eq]

/-- Mentioned ⟹ the waived quote is the core quote.
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
lemma waivedQuote_of_mentionedBy (DP : DeductiveProcess) (ov : Overlay) (W : Finset ℕ)
    (pre : ℕ → RationalBeliefState) {n : ℕ} {φ : Sentence}
    (h : MentionedBy (waivedFirm DP ov W pre n) φ) :
    waivedQuote DP ov W pre n φ = (waivedCore DP ov W pre n).quote φ := by
  rw [waivedQuote_eq, if_pos ((mem_mentionedSet_iff _ φ).mpr h)]

/-- Every waived quote lies in `[0,1]`.
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
lemma waivedQuote_mem_Icc (DP : DeductiveProcess) (ov : Overlay) (W : Finset ℕ)
    (pre : ℕ → RationalBeliefState) (n : ℕ) (φ : Sentence) :
    0 ≤ waivedQuote DP ov W pre n φ ∧ waivedQuote DP ov W pre n φ ≤ 1 := by
  rw [waivedQuote_eq]
  split_ifs
  · exact RationalBeliefState.quote_mem_Icc _ φ
  · exact ov.range _ _ _ _

/-- Below `n`, `waivedBelow n` is the waived table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma waivedBelow_of_lt (DP : DeductiveProcess) (ov : Overlay) (W : Finset ℕ)
    (pre : ℕ → RationalBeliefState) {n k : ℕ} (h : k < n) (φ : Sentence) :
    waivedBelow DP ov W pre n k φ = waivedQuote DP ov W pre k φ := by
  simp [waivedBelow, h]

/-- The wrong-market guard for the waived recursion: its firm is the static firm on the waived table.
Source: [[bli-overlay-mandate]] T7; T4 traps (i)
Kind: L
Fidelity: exact -/
lemma waivedFirm_eq (DP : DeductiveProcess) (ov : Overlay) (W : Finset ℕ)
    (pre : ℕ → RationalBeliefState) (n : ℕ) :
    waivedFirm DP ov W pre n = TradingFirmAt DP (waivedQuote DP ov W pre) n := by
  unfold waivedFirm
  apply TradingFirmAt_eq_of_eq_prefix
  intro day hday φ
  exact waivedBelow_of_lt DP ov W pre hday φ

/-- On a searched day the core state is accepted for the past-view strategy against the core past.
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
lemma waivedCore_accepts (DP : DeductiveProcess) (ov : Overlay) (W : Finset ℕ)
    (pre : ℕ → RationalBeliefState) {n : ℕ} (hn : n ∉ W) :
    MarketMakerAccepts (waivedPv DP ov W pre n) (waivedPast DP ov W pre n) (marketMakerError n)
      (waivedCore DP ov W pre n) := by
  rw [waivedCore_of_not_mem DP ov W pre hn]
  exact MarketMaker_accepts _ _ _ _

/-! ## T7: no e.c. trader exploits the waived recursion -/

/-- **T7, the day bound off `W`.** On every searched day, the firm's day strategy on the waived
table has value at most `marketMakerError n` on the waived history in every p.c. world — through
the customer's entry point `dayValue_le_of_accepted_state_subst`.
Source: [[bli-overlay-mandate]] T7
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem waived_firm_dayValue_le (DP : DeductiveProcess) (ov : Overlay) (W : Finset ℕ)
    (pre : ℕ → RationalBeliefState) {n : ℕ} (hn : n ∉ W) (v : PCWorld) :
    (TradingFirmAt DP (waivedQuote DP ov W pre) n).value (waivedHistory DP ov W pre) v.payout ≤
      (marketMakerError n : ℝ) := by
  rw [← waivedFirm_eq]
  exact dayValue_le_of_accepted_state_subst (waivedFirm DP ov W pre n) (waivedBelow DP ov W pre n)
    (waivedPast DP ov W pre n) (marketMakerError n) (waivedCore DP ov W pre n)
    (waivedCore_accepts DP ov W pre hn) (waivedHistory DP ov W pre)
    (fun φ _ k hk => by
      show (waivedQuote DP ov W pre k φ : ℝ) = _
      rw [waivedBelow_of_lt DP ov W pre hk])
    (fun φ hφ => by
      show (waivedQuote DP ov W pre n φ : ℝ) = _
      rw [waivedQuote_of_mentionedBy DP ov W pre hφ]) v

/-- **T7. No efficiently computable trader exploits the waived recursion**, for every process,
overlay, finite waived set and prescribed tables: T3(c) at the waived table with the day bound off
`W`.
Source: [[bli-overlay-mandate]] T7; [[bli-program]] §3.3 (iii), §3.6 (vi)
Kind: C
Fidelity: exact
Hyps: (a) — `trading_firm_dominance` and `MarketMaker_accepts` are FAF theorems, applied; `ov.range` is a field of D2; nothing is assumed of `pre` -/
theorem waived_no_ec_trader_exploits (DP : DeductiveProcess) (ov : Overlay) (W : Finset ℕ)
    (pre : ℕ → RationalBeliefState) (Tr : Trader) (hTr : EfficientlyComputable Tr) :
    ¬ Tr.Exploits (waivedHistory DP ov W pre) DP :=
  no_ec_trader_exploits_of_firm_accepted_off_finite DP (waivedQuote DP ov W pre)
    (waivedQuote_mem_Icc DP ov W pre) W
    (fun _ hn v => waived_firm_dayValue_le DP ov W pre hn v) Tr hTr

/-! ## Cross-check: with `W = ∅` the waived recursion is the overlaid recursion -/

/-- With no waived days the waived recursion is the plain overlaid recursion (core states and
quotes), by strong induction: the firms agree on the prefix, the pasts agree, and the market maker
is run on the same inputs.
Source: [[bli-overlay-mandate]] T7 ("state T4 as the `W = ∅` instance")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem waived_empty_eq (DP : DeductiveProcess) (ov : Overlay) (pre : ℕ → RationalBeliefState)
    (n : ℕ) :
    waivedCore DP ov ∅ pre n = coreState DP ov n ∧
      ∀ φ, waivedQuote DP ov ∅ pre n φ = overlayQuote DP ov n φ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hpast : waivedPast DP ov ∅ pre n = corePast DP ov n := by
        apply List.ext_getElem
        · simp [waivedPast, corePast]
        · intro i hi₁ hi₂
          simp only [waivedPast, corePast, List.getElem_ofFn]
          exact (ih i (by simpa [waivedPast] using hi₁)).1
      have hbelow : waivedBelow DP ov ∅ pre n = quoteBelow DP ov n := by
        funext k φ
        unfold waivedBelow quoteBelow
        split_ifs with hk
        · exact (ih k hk).2 φ
        · rfl
      have hfirm : waivedFirm DP ov ∅ pre n = firmStrat DP ov n := by
        unfold waivedFirm firmStrat
        rw [hbelow]
      have hpv : waivedPv DP ov ∅ pre n = pvStrat DP ov n := by
        unfold waivedPv pvStrat
        rw [hbelow, hfirm]
      have hcore : waivedCore DP ov ∅ pre n = coreState DP ov n := by
        rw [waivedCore_of_not_mem DP ov ∅ pre (Finset.notMem_empty n), coreState_eq, hpv, hpast]
      refine ⟨hcore, fun φ => ?_⟩
      rw [waivedQuote_eq, overlayQuote_eq, hfirm, hcore, hpast]

/-- The market form of the cross-check.
Source: [[bli-overlay-mandate]] T7
Kind: P
Fidelity: exact -/
theorem waivedHistory_empty_eq (DP : DeductiveProcess) (ov : Overlay)
    (pre : ℕ → RationalBeliefState) : waivedHistory DP ov ∅ pre = overlayHistory DP ov := by
  funext n φ
  unfold waivedHistory overlayHistory
  rw [(waived_empty_eq DP ov pre n).2 φ]

end Cleanroom.Bli.BliOverlay.AttemptB
