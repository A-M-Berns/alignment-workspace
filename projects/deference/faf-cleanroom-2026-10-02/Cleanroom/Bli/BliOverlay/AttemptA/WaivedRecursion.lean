import Cleanroom.Bli.BliOverlay.AttemptA.Recursion

/-!
# `bli-overlay` (attempt A) · WaivedRecursion: the recursion with prescribed days (T7)

**T7 (extension).** The same recursion as `Recursion.lean`, except that on the days of a finite
set `W` the core state is a **prescribed** finite table `pre n` instead of the market maker's
search; the firm is still built from the overlaid past on every day, and the overlaid quote is
still the core quote on the mentioned set and `ov` elsewhere. On angle A this is immediate: the
day step `waivedCore` skips the search exactly on `W`.

* `waivedRec`, `waivedCoreState`, `waivedQuote`, `waivedHistory`, `waivedFirmStrat` — the
  definitions, mirroring D3; `waivedCoreState_of_mem` (`= pre n` on `W`) and
  `waivedCoreState_accepts` (accepted by the market maker off `W`).
* `waived_firm_dayValue_le` (off `W`), `waived_firm_not_exploited` (T3(a) with this `W`), and
  **`waived_no_ec_trader_exploits`**: no efficiently computable trader exploits the waived
  overlaid market — the shape `bli-exact-base` K7 (the finite-segment splice) and B3's initial
  segments need ([[bli-program]] §3.3 (iii), §3.6 (vi)).
* `waivedRec_empty` / `waivedQuote_empty`: with `W = ∅` the waived recursion **is** `dayRec`, so
  T4 is the `W = ∅` instance of T7 — and this is the `W ≠ ∅`-capable construction that exercises
  the waived part of T3(a) (findings F-12).

Sources: [[bli-overlay-mandate]] T7; [[bli-program]] §3.3 (iii), §3.6 (vi).
-/

namespace Cleanroom.Bli.BliOverlay.AttemptA

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

noncomputable section

/-- The day-`n` core state of the waived recursion: the prescribed table on `W`, the market
maker's output elsewhere.
Source: [[bli-overlay-mandate]] T7
Kind: D
Fidelity: exact -/
def waivedCore (W : Finset ℕ) (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess) (n : ℕ)
    (prev : Fin n → DayRecord) : RationalBeliefState :=
  if n ∈ W then pre n else dayCore DP n prev

/-- One step of the waived recursion.
Source: [[bli-overlay-mandate]] T7
Kind: D
Fidelity: exact -/
def waivedStep (W : Finset ℕ) (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess)
    (ov : Overlay) (n : ℕ) (prev : Fin n → DayRecord) : DayRecord where
  core := waivedCore W pre DP n prev
  quote φ := if φ ∈ mentionedSet (dayStrat DP n prev) then (waivedCore W pre DP n prev).quote φ
    else ov.val n (List.ofFn fun i => (prev i).core) (waivedCore W pre DP n prev) φ
  range φ := by
    by_cases h : φ ∈ mentionedSet (dayStrat DP n prev)
    · rw [if_pos h]
      exact (waivedCore W pre DP n prev).quote_mem_Icc φ
    · rw [if_neg h]
      exact ov.range _ _ _ _

/-- **T7. The waived recursion** (well-founded on the day).
Source: [[bli-overlay-mandate]] T7
Kind: D
Fidelity: exact -/
def waivedRec (W : Finset ℕ) (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess)
    (ov : Overlay) : ℕ → DayRecord
  | n => waivedStep W pre DP ov n (fun i : Fin n => waivedRec W pre DP ov i)
termination_by n => n
decreasing_by exact i.isLt

/-- The waived recursion's core state.
Source: [[bli-overlay-mandate]] T7
Kind: D
Fidelity: exact -/
def waivedCoreState (W : Finset ℕ) (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess)
    (ov : Overlay) (n : ℕ) : RationalBeliefState :=
  (waivedRec W pre DP ov n).core

/-- The waived recursion's overlaid table.
Source: [[bli-overlay-mandate]] T7
Kind: D
Fidelity: exact -/
def waivedQuote (W : Finset ℕ) (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess)
    (ov : Overlay) : ℕ → Sentence → ℚ :=
  fun n φ => (waivedRec W pre DP ov n).quote φ

/-- The waived recursion's market.
Source: [[bli-overlay-mandate]] T7
Kind: D
Fidelity: exact -/
def waivedHistory (W : Finset ℕ) (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess)
    (ov : Overlay) : History :=
  fun n φ => (waivedQuote W pre DP ov n φ : ℝ)

/-- The waived recursion's day-`n` firm: the trading firm built from the waived overlaid table.
Source: [[bli-overlay-mandate]] T7
Kind: D
Fidelity: exact -/
def waivedFirmStrat (W : Finset ℕ) (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess)
    (ov : Overlay) (n : ℕ) : Strategy n :=
  TradingFirmAt DP (waivedQuote W pre DP ov) n

/-- `waivedQuote` is in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma waivedQuote_range (W : Finset ℕ) (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess)
    (ov : Overlay) : ∀ k φ, 0 ≤ waivedQuote W pre DP ov k φ ∧ waivedQuote W pre DP ov k φ ≤ 1 :=
  fun k φ => (waivedRec W pre DP ov k).range φ

/-- The restricted waived past of day `n`.
Source: [[bli-overlay-mandate]] T7
Kind: D
Fidelity: exact -/
def waivedRestrictedPast (W : Finset ℕ) (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess)
    (ov : Overlay) (n : ℕ) : List RationalBeliefState :=
  restrictedPast (mentionedSet (waivedFirmStrat W pre DP ov n)) (waivedQuote W pre DP ov)
    (waivedQuote_range W pre DP ov) n

/-- The `def:market` range clause for the waived market.
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
lemma waivedHistory_range (W : Finset ℕ) (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess)
    (ov : Overlay) :
    ∀ day φ, 0 ≤ waivedHistory W pre DP ov day φ ∧ waivedHistory W pre DP ov day φ ≤ 1 := by
  intro d φ
  unfold waivedHistory
  exact ⟨by exact_mod_cast (waivedQuote_range W pre DP ov d φ).1,
    by exact_mod_cast (waivedQuote_range W pre DP ov d φ).2⟩

/-- The waived market is the cast of its rational table.
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
lemma waivedHistory_eq_quote_cast (W : Finset ℕ) (pre : ℕ → RationalBeliefState)
    (DP : DeductiveProcess) (ov : Overlay) (day : ℕ) (φ : Sentence) :
    waivedHistory W pre DP ov day φ = (waivedQuote W pre DP ov day φ : ℝ) := rfl

/-- The recursion's equation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma waivedRec_unfold (W : Finset ℕ) (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess)
    (ov : Overlay) (n : ℕ) :
    waivedRec W pre DP ov n = waivedStep W pre DP ov n (fun i : Fin n => waivedRec W pre DP ov i) := by
  rw [waivedRec]

/-- The previous-records table of the waived recursion is its table on days `< n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prevTable_waivedRec (W : Finset ℕ) (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess)
    (ov : Overlay) (n : ℕ) {k : ℕ} (hk : k < n) (φ : Sentence) :
    prevTable n (fun i : Fin n => waivedRec W pre DP ov i) k φ = waivedQuote W pre DP ov k φ := by
  rw [prevTable_of_lt n _ hk]
  rfl

/-- The waived recursion's day-`n` strategy is `waivedFirmStrat`.
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
lemma dayStrat_eq_waivedFirmStrat (W : Finset ℕ) (pre : ℕ → RationalBeliefState)
    (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    dayStrat DP n (fun i : Fin n => waivedRec W pre DP ov i) = waivedFirmStrat W pre DP ov n := by
  unfold dayStrat waivedFirmStrat
  apply TradingFirmAt_eq_of_eq_prefix
  intro k hk φ
  exact prevTable_waivedRec W pre DP ov n hk φ

/-- The day-`n` record's core, unfolded one step.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma waivedRec_core (W : Finset ℕ) (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess)
    (ov : Overlay) (n : ℕ) :
    (waivedRec W pre DP ov n).core = waivedCore W pre DP n (fun i : Fin n => waivedRec W pre DP ov i) := by
  rw [waivedRec_unfold]
  rfl

/-- The day-`n` record's quote, unfolded one step.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma waivedRec_quote (W : Finset ℕ) (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess)
    (ov : Overlay) (n : ℕ) (φ : Sentence) :
    (waivedRec W pre DP ov n).quote φ =
      if φ ∈ mentionedSet (dayStrat DP n (fun i : Fin n => waivedRec W pre DP ov i)) then
        (waivedCore W pre DP n (fun i : Fin n => waivedRec W pre DP ov i)).quote φ
      else ov.val n (List.ofFn fun i : Fin n => (waivedRec W pre DP ov i).core)
        (waivedCore W pre DP n (fun i : Fin n => waivedRec W pre DP ov i)) φ := by
  conv_lhs => rw [waivedRec_unfold]
  rfl

/-- **On a waived day the core state is the prescribed table.**
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
lemma waivedCoreState_of_mem (W : Finset ℕ) (pre : ℕ → RationalBeliefState)
    (DP : DeductiveProcess) (ov : Overlay) {n : ℕ} (hn : n ∈ W) :
    waivedCoreState W pre DP ov n = pre n := by
  unfold waivedCoreState
  rw [waivedRec_core, waivedCore, if_pos hn]

/-- **Off `W` the core state is the market maker's output** against `waivedFirmStrat n` and the
restricted waived past.
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
lemma waivedCoreState_eq_of_not_mem (W : Finset ℕ) (pre : ℕ → RationalBeliefState)
    (DP : DeductiveProcess) (ov : Overlay) {n : ℕ} (hn : n ∉ W) :
    waivedCoreState W pre DP ov n = MarketMaker (waivedFirmStrat W pre DP ov n)
      (waivedRestrictedPast W pre DP ov n) (marketMakerError n) (marketMakerError_pos n) := by
  unfold waivedCoreState
  rw [waivedRec_core, waivedCore, if_neg hn]
  unfold dayCore dayPast
  rw [dayStrat_eq_waivedFirmStrat]
  unfold waivedRestrictedPast
  congr 1
  apply restrictedPast_congr
  intro k hk φ _
  exact prevTable_waivedRec W pre DP ov n hk φ

/-- Off `W` the core state is accepted by the market maker.
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
lemma waivedCoreState_accepts (W : Finset ℕ) (pre : ℕ → RationalBeliefState)
    (DP : DeductiveProcess) (ov : Overlay) {n : ℕ} (hn : n ∉ W) :
    MarketMakerAccepts (waivedFirmStrat W pre DP ov n) (waivedRestrictedPast W pre DP ov n)
      (marketMakerError n) (waivedCoreState W pre DP ov n) := by
  rw [waivedCoreState_eq_of_not_mem W pre DP ov hn]
  exact MarketMaker_accepts _ _ _ _

/-- The waived quote, as a case split on the mentioned set.
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
lemma waivedQuote_eq_ite (W : Finset ℕ) (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess)
    (ov : Overlay) (n : ℕ) (φ : Sentence) :
    waivedQuote W pre DP ov n φ =
      if φ ∈ mentionedSet (waivedFirmStrat W pre DP ov n) then (waivedCoreState W pre DP ov n).quote φ
      else ov.val n (List.ofFn fun i : Fin n => waivedCoreState W pre DP ov i)
        (waivedCoreState W pre DP ov n) φ := by
  unfold waivedQuote
  rw [waivedRec_quote, dayStrat_eq_waivedFirmStrat, ← waivedRec_core]
  rfl

/-- On the mentioned set, the waived quote is the core quote.
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
lemma waivedQuote_of_mem (W : Finset ℕ) (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess)
    (ov : Overlay) {n : ℕ} {φ : Sentence} (h : φ ∈ mentionedSet (waivedFirmStrat W pre DP ov n)) :
    waivedQuote W pre DP ov n φ = (waivedCoreState W pre DP ov n).quote φ := by
  rw [waivedQuote_eq_ite, if_pos h]

/-! ## T7: no e.c. trader exploits the waived market -/

/-- **T7, the day bound off `W`.**
Source: [[bli-overlay-mandate]] T7
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem waived_firm_dayValue_le (W : Finset ℕ) (pre : ℕ → RationalBeliefState)
    (DP : DeductiveProcess) (ov : Overlay) {n : ℕ} (hn : n ∉ W) :
    ∀ v : PCWorld, (waivedFirmStrat W pre DP ov n).value (waivedHistory W pre DP ov) v.payout ≤
      (marketMakerError n : ℝ) := by
  apply dayValue_le_of_accepts (waivedFirmStrat W pre DP ov n) (waivedRestrictedPast W pre DP ov n)
    (marketMakerError n) (waivedCoreState W pre DP ov n) (waivedCoreState_accepts W pre DP ov hn)
  intro φ hφ k hk
  rw [waivedHistory_eq_quote_cast]
  congr 1
  rcases Nat.lt_or_eq_of_le hk with hlt | rfl
  · rw [candidateRationalHistory, Function.update_of_ne (Nat.ne_of_lt hlt)]
    unfold waivedRestrictedPast
    exact (rationalHistory_restrictedPast hlt (mem_mentionedSet_iff.mpr hφ)).symm
  · rw [candidateRationalHistory, Function.update_self]
    exact waivedQuote_of_mem W pre DP ov (mem_mentionedSet_iff.mpr hφ)

/-- **T7. The firm does not exploit the waived market**: T3(a) with this `W`.
Source: [[bli-overlay-mandate]] T7; [[bli-program]] §3.3 (iii)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem waived_firm_not_exploited (W : Finset ℕ) (pre : ℕ → RationalBeliefState)
    (DP : DeductiveProcess) (ov : Overlay) :
    ¬ (tradingFirmTrader DP (waivedQuote W pre DP ov)).Exploits (waivedHistory W pre DP ov) DP :=
  not_exploits_of_dayValue_le_off_finite _ _ DP (waivedHistory_range W pre DP ov) W
    (fun n hn v => waived_firm_dayValue_le W pre DP ov hn v)

/-- **T7 (headline). No efficiently computable trader exploits the waived overlaid market**, for
every finite `W`, every prescribed table `pre`, every process and every overlay.
Source: [[bli-overlay-mandate]] T7; [[bli-program]] §3.3 (iii), §3.6 (vi)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem waived_no_ec_trader_exploits (W : Finset ℕ) (pre : ℕ → RationalBeliefState)
    (DP : DeductiveProcess) (ov : Overlay) (Tr : Trader) (hTr : EfficientlyComputable Tr) :
    ¬ Tr.Exploits (waivedHistory W pre DP ov) DP := by
  intro hex
  have hfirm := trading_firm_dominance DP (waivedHistory W pre DP ov)
    (waivedHistory_range W pre DP ov) (waivedQuote W pre DP ov)
    (waivedHistory_eq_quote_cast W pre DP ov) Tr hTr hex
  exact waived_firm_not_exploited W pre DP ov hfirm

/-! ## `W = ∅` is the unwaived recursion -/

/-- With `W = ∅` the waived step is the unwaived step.
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
lemma waivedStep_empty (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess) (ov : Overlay)
    (n : ℕ) (prev : Fin n → DayRecord) :
    waivedStep ∅ pre DP ov n prev = dayStep DP ov n prev := by
  have hcore : waivedCore ∅ pre DP n prev = dayCore DP n prev := by
    unfold waivedCore
    rw [if_neg (Finset.notMem_empty n)]
  unfold waivedStep dayStep
  simp only [hcore]

/-- **With `W = ∅` the waived recursion is `dayRec`**: T4 is the `W = ∅` instance of T7.
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
theorem waivedRec_empty (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess) (ov : Overlay)
    (n : ℕ) : waivedRec ∅ pre DP ov n = dayRec DP ov n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [waivedRec_unfold, dayRec_unfold]
    have hprev : (fun i : Fin n => waivedRec ∅ pre DP ov i) = fun i : Fin n => dayRec DP ov i :=
      funext fun i => ih i i.isLt
    rw [hprev, waivedStep_empty]

/-- With `W = ∅` the waived table is `overlayQuote`.
Source: [[bli-overlay-mandate]] T7
Kind: L
Fidelity: exact -/
theorem waivedQuote_empty (pre : ℕ → RationalBeliefState) (DP : DeductiveProcess) (ov : Overlay) :
    waivedQuote ∅ pre DP ov = overlayQuote DP ov := by
  funext n φ
  unfold waivedQuote overlayQuote
  rw [waivedRec_empty]

end

end Cleanroom.Bli.BliOverlay.AttemptA
