import Cleanroom.Bli.BliOverlay.AttemptB.Waived
import LogicalInduction.Construction.LIA

/-!
# `bli-overlay` (attempt B) · Recursion: overlays (D2), the overlaid recursion (D3) and L6(a) (T4)

**The construction-facing file** (plan §0.5), kept separate from the lemmas it uses.

* **D2.** `Overlay`: a function of finite data — the day `n`, the list of the days-`< n` core
  states, the day-`n` core state — returning the day-`n` price of an unmentioned sentence, with
  the `[0,1]` range as a structure field (never a clamp). `Overlay.zero` and `Overlay.half`.
* **D3 (angle B).** `overlayDay DP ov n` returns, by well-founded recursion on the day, the pair
  (core state, day-`n` overlaid quote). On day `n`: the **overlaid table below `n`** is
  `quoteBelow`; the firm's day strategy is built from it, `firmStrat n = TradingFirmAt DP
  (quoteBelow n) n`; the **past-view strategy** `pvStrat n` substitutes every day-`< n` price
  leaf of `firmStrat n` by the overlaid value (`Strategy.substPast`); the core state is FAF's
  `MarketMaker (pvStrat n) (corePast n) (marketMakerError n)`; and the overlaid quote is the core
  quote on `mentionedSet (firmStrat n)` and `ov` off it. `overlayQuote`, `overlayHistory`,
  `coreState`, `corePast`, `firmStrat`, `pvStrat`, `coreHistory` are the named projections and
  `overlayDay_eq` is the one-step unfolding they all rest on. `firmStrat_eq` (the firm equals the
  static complete-table firm on the overlaid table) is the wrong-market guard in identity form.
* **The past-view trader.** `pvTrader DP ov` plays `pvStrat n` on day `n`; the core states are
  exactly FAF's generic `marketMakerStates (pvTrader DP ov)` (`coreState_eq_marketMakerStates`,
  the pattern of `liaStates_eq_marketMakerStates`), so FAF's `marketMaker_day_value_le` and
  `marketMaker_not_exploited` apply **unchanged** to `pvTrader` — and transfer to the firm on the
  overlaid history by the exact per-day value identity `pvStrat_value_eq` (the substitution lemma
  plus T1).
* **T4.** `overlay_firm_dayValue_le` (also derived a second, independent way through the
  customer's entry point `dayValue_le_of_accepted_state_subst`: `overlay_firm_dayValue_le_via_accepted`),
  `overlay_firm_not_exploited` (transport of `marketMaker_not_exploited`; also derived from T3(a)
  with `W = ∅`: `overlay_firm_not_exploited_via_waived`), the headline
  `overlay_no_ec_trader_exploits`, the assembly lemma
  `overlay_isLogicalInductor_of_computableMarket` (Kind L; market computability **assumed**), and
  the sanity identity `overlayQuote_zero_eq_liaQuote` (with the zero overlay the recursion **is**
  FAF's LIA, through `MarketMaker_congr` and `marketMakerAccepts_substPast_iff`).
-/

namespace Cleanroom.Bli.BliOverlay.AttemptB

open LogicalInduction Cleanroom.Bli.BliFound

/-! ## D2: overlays -/

/-- **D2. An overlay**: the day-`n` price of an unmentioned sentence, as a function of the day, the
days-`< n` core states and the day-`n` core state, with values in `[0,1]` (a structure field, not
a clamp).
Source: [[bli-overlay-mandate]] D2; [[bli-program]] §3.3 (ii)
Kind: D
Fidelity: exact -/
structure Overlay where
  /-- The overlaid price of `φ` on day `n`, given the core past and the day-`n` core state. -/
  val : ℕ → List RationalBeliefState → RationalBeliefState → Sentence → ℚ
  /-- The `def:market` range clause, carried as data. -/
  range : ∀ n past B φ, 0 ≤ val n past B φ ∧ val n past B φ ≤ 1

/-- The zero overlay: every unmentioned sentence is quoted `0`, as FAF's LIA does.
Source: [[bli-overlay-mandate]] T4 (v)
Kind: D
Fidelity: exact -/
def Overlay.zero : Overlay := ⟨fun _ _ _ _ => 0, fun _ _ _ _ => by norm_num⟩

/-- The constant-half overlay: every unmentioned sentence is quoted `1/2` (the T5 witness).
Source: [[bli-overlay-mandate]] T5
Kind: D
Fidelity: exact -/
def Overlay.half : Overlay := ⟨fun _ _ _ _ => 1 / 2, fun _ _ _ _ => by norm_num⟩

/-! ## D3: the overlaid recursion (angle B) -/

/-- **D3 (angle B). One day of the overlaid recursion**: the pair (day-`n` core state, day-`n`
overlaid quote). The firm is built from the overlaid table below `n`; the market maker is run on
the past-view strategy (day-`< n` leaves substituted by the overlaid values) against the core
past; the overlaid quote is the core quote on the firm's mentioned set and `ov` off it.
Source: [[bli-overlay-mandate]] D3, §Attempt angles (B); [[bli-program]] §3.3 (ii)
Kind: D
Fidelity: exact -/
noncomputable def overlayDay (DP : DeductiveProcess) (ov : Overlay) :
    ℕ → RationalBeliefState × (Sentence → ℚ)
  | n =>
      let past : List RationalBeliefState := List.ofFn fun i : Fin n => (overlayDay DP ov i).1
      let below : ℕ → Sentence → ℚ :=
        fun k φ => if _h : k < n then (overlayDay DP ov k).2 φ else 0
      let firm : Strategy n := TradingFirmAt DP below n
      let B : RationalBeliefState :=
        MarketMaker (Strategy.substPast below firm) past (marketMakerError n) (marketMakerError_pos n)
      (B, fun φ => if φ ∈ mentionedSet firm then B.quote φ else ov.val n past B φ)
termination_by n => n
decreasing_by
  all_goals first | exact i.isLt | exact _h

/-- The day-`n` core state.
Source: [[bli-overlay-mandate]] D3
Kind: D
Fidelity: exact -/
noncomputable def coreState (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) : RationalBeliefState :=
  (overlayDay DP ov n).1

/-- The overlaid exact rational quote table.
Source: [[bli-overlay-mandate]] D3
Kind: D
Fidelity: exact -/
noncomputable def overlayQuote (DP : DeductiveProcess) (ov : Overlay) : ℕ → Sentence → ℚ :=
  fun n φ => (overlayDay DP ov n).2 φ

/-- The core past: the list of the days-`< n` core states.
Source: [[bli-overlay-mandate]] D3
Kind: D
Fidelity: exact -/
noncomputable def corePast (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) : List RationalBeliefState :=
  List.ofFn fun i : Fin n => coreState DP ov i

/-- The overlaid table restricted to days `< n` (`0` from day `n` on).
Source: [[bli-overlay-mandate]] D3
Kind: D
Fidelity: exact -/
noncomputable def quoteBelow (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) : ℕ → Sentence → ℚ :=
  fun k φ => if k < n then overlayQuote DP ov k φ else 0

/-- The firm's day-`n` strategy, **built from the overlaid table** below `n`.
Source: [[bli-overlay-mandate]] D3
Kind: D
Fidelity: exact -/
noncomputable def firmStrat (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) : Strategy n :=
  TradingFirmAt DP (quoteBelow DP ov n) n

/-- The past-view strategy: `firmStrat n` with every day-`< n` price leaf substituted by the
overlaid value.
Source: [[bli-overlay-mandate]] §Attempt angles (B)
Kind: D
Fidelity: exact -/
noncomputable def pvStrat (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) : Strategy n :=
  Strategy.substPast (quoteBelow DP ov n) (firmStrat DP ov n)

/-- The overlaid real market: the cast of `overlayQuote`.
Source: [[bli-overlay-mandate]] D3
Kind: D
Fidelity: exact -/
noncomputable def overlayHistory (DP : DeductiveProcess) (ov : Overlay) : History :=
  fun n φ => (overlayQuote DP ov n φ : ℝ)

/-- The core real market: the cast of the core states' quotes (`0` off their supports).
Source: [[bli-overlay-mandate]] §Attempt angles (B)
Kind: D
Fidelity: exact -/
noncomputable def coreHistory (DP : DeductiveProcess) (ov : Overlay) : History :=
  fun n φ => (coreState DP ov n).toValuation φ

/-- **The one-step unfolding** of the recursion in terms of the named projections.
Source: [[bli-overlay-mandate]] D3
Kind: L
Fidelity: exact -/
lemma overlayDay_eq (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    overlayDay DP ov n =
      (MarketMaker (pvStrat DP ov n) (corePast DP ov n) (marketMakerError n) (marketMakerError_pos n),
       fun φ => if φ ∈ mentionedSet (firmStrat DP ov n) then
          (MarketMaker (pvStrat DP ov n) (corePast DP ov n) (marketMakerError n)
            (marketMakerError_pos n)).quote φ
        else ov.val n (corePast DP ov n)
          (MarketMaker (pvStrat DP ov n) (corePast DP ov n) (marketMakerError n)
            (marketMakerError_pos n)) φ) := by
  rw [overlayDay]
  rfl

/-- The core state is the market maker's fixed point against the past-view strategy on the core past.
Source: [[bli-overlay-mandate]] D3
Kind: L
Fidelity: exact -/
lemma coreState_eq (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    coreState DP ov n =
      MarketMaker (pvStrat DP ov n) (corePast DP ov n) (marketMakerError n) (marketMakerError_pos n) := by
  unfold coreState
  rw [overlayDay_eq]

/-- The overlaid quote, unfolded: core quote on the mentioned set, `ov` off it.
Source: [[bli-overlay-mandate]] D3
Kind: L
Fidelity: exact -/
lemma overlayQuote_eq (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) (φ : Sentence) :
    overlayQuote DP ov n φ =
      if φ ∈ mentionedSet (firmStrat DP ov n) then (coreState DP ov n).quote φ
      else ov.val n (corePast DP ov n) (coreState DP ov n) φ := by
  unfold overlayQuote
  rw [overlayDay_eq, coreState_eq]

/-- Mentioned ⟹ the overlaid quote is the core quote.
Source: [[bli-overlay-mandate]] D3 (`overlayQuote_of_mem`)
Kind: L
Fidelity: exact -/
lemma overlayQuote_of_mem (DP : DeductiveProcess) (ov : Overlay) {n : ℕ} {φ : Sentence}
    (h : φ ∈ mentionedSet (firmStrat DP ov n)) :
    overlayQuote DP ov n φ = (coreState DP ov n).quote φ := by
  rw [overlayQuote_eq, if_pos h]

/-- Unmentioned ⟹ the overlaid quote is the overlay's value.
Source: [[bli-overlay-mandate]] D3 (`overlayQuote_of_not_mem`)
Kind: L
Fidelity: exact -/
lemma overlayQuote_of_not_mem (DP : DeductiveProcess) (ov : Overlay) {n : ℕ} {φ : Sentence}
    (h : φ ∉ mentionedSet (firmStrat DP ov n)) :
    overlayQuote DP ov n φ = ov.val n (corePast DP ov n) (coreState DP ov n) φ := by
  rw [overlayQuote_eq, if_neg h]

/-- `overlayQuote_of_mem` in `MentionedBy` form.
Source: [[bli-overlay-mandate]] D3
Kind: L
Fidelity: exact -/
lemma overlayQuote_of_mentionedBy (DP : DeductiveProcess) (ov : Overlay) {n : ℕ} {φ : Sentence}
    (h : MentionedBy (firmStrat DP ov n) φ) :
    overlayQuote DP ov n φ = (coreState DP ov n).quote φ :=
  overlayQuote_of_mem DP ov ((mem_mentionedSet_iff _ φ).mpr h)

/-- Every overlaid quote lies in `[0,1]` (from `RationalBeliefState.quote_mem_Icc` and `ov.range`).
Source: [[bli-overlay-mandate]] D3 (`overlayHistory_range`)
Kind: L
Fidelity: exact -/
lemma overlayQuote_mem_Icc (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) (φ : Sentence) :
    0 ≤ overlayQuote DP ov n φ ∧ overlayQuote DP ov n φ ≤ 1 := by
  rw [overlayQuote_eq]
  split_ifs
  · exact RationalBeliefState.quote_mem_Icc _ φ
  · exact ov.range _ _ _ _

/-- The `def:market` range clause for the overlaid market.
Source: [[bli-overlay-mandate]] D3 (`overlayHistory_range`)
Kind: L
Fidelity: exact -/
lemma overlayHistory_range (DP : DeductiveProcess) (ov : Overlay) (day : ℕ) (φ : Sentence) :
    0 ≤ overlayHistory DP ov day φ ∧ overlayHistory DP ov day φ ≤ 1 := by
  unfold overlayHistory
  exact ⟨by exact_mod_cast (overlayQuote_mem_Icc DP ov day φ).1,
    by exact_mod_cast (overlayQuote_mem_Icc DP ov day φ).2⟩

/-- The overlaid market is definitionally the cast of the overlaid table.
Source: [[bli-overlay-mandate]] D3 (`overlayHistory_eq_quote_cast`)
Kind: L
Fidelity: exact -/
lemma overlayHistory_eq_quote_cast (DP : DeductiveProcess) (ov : Overlay) (day : ℕ) (φ : Sentence) :
    overlayHistory DP ov day φ = (overlayQuote DP ov day φ : ℝ) := rfl

/-- Below `n`, `quoteBelow n` is the overlaid table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma quoteBelow_of_lt (DP : DeductiveProcess) (ov : Overlay) {n k : ℕ} (h : k < n) (φ : Sentence) :
    quoteBelow DP ov n k φ = overlayQuote DP ov k φ := by
  simp [quoteBelow, h]

/-- **The wrong-market guard.** The firm's day-`n` strategy is the static complete-table firm's
day-`n` strategy on the overlaid table: `tradingFirmTrader DP (overlayQuote DP ov)` is the trader
`trading_firm_dominance` quantifies over, and it is *this* firm the recursion runs.
Source: [[bli-overlay-mandate]] D3 (`firmStrat_eq`); T4 traps (i)
Kind: L
Fidelity: exact -/
lemma firmStrat_eq (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    firmStrat DP ov n = TradingFirmAt DP (overlayQuote DP ov) n := by
  unfold firmStrat
  apply TradingFirmAt_eq_of_eq_prefix
  intro day hday φ
  exact quoteBelow_of_lt DP ov hday φ

/-- Inside the core past, the rational history reads the core states' quotes.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma rationalHistory_corePast (DP : DeductiveProcess) (ov : Overlay) {n k : ℕ} (h : k < n)
    (φ : Sentence) : rationalHistory (corePast DP ov n) k φ = (coreState DP ov k).quote φ := by
  simp [rationalHistory, corePast, h]

/-- The day-`n` core state is accepted by the market maker for the past-view strategy against the
core past (FAF's `MarketMaker_accepts` at the recursion).
Source: [[bli-overlay-mandate]] §Attempt angles (B)
Kind: L
Fidelity: exact -/
lemma coreState_accepts (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    MarketMakerAccepts (pvStrat DP ov n) (corePast DP ov n) (marketMakerError n) (coreState DP ov n) := by
  rw [coreState_eq]
  exact MarketMaker_accepts _ _ _ _

/-- The core state's support is inside the firm's support (hence inside its mentioned set).
Source: [[bli-overlay-mandate]] §Context (i)
Kind: L
Fidelity: exact -/
lemma coreState_support_subset (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    (coreState DP ov n).support ⊆ (firmStrat DP ov n).support := by
  have h := (coreState_accepts DP ov n).1
  unfold pvStrat at h
  rwa [Strategy.support_substPast] at h

/-! ## The past-view trader and the identification with `marketMakerStates` -/

/-- **The past-view trader**: on day `n` it plays the past-view strategy `pvStrat DP ov n`.
Defined after the states (its day-`n` strategy reads the overlaid days `< n`, which are functions
of the states), exactly as FAF defines `liaTrader` after `liaStates` (Known issue 3).
Source: [[bli-overlay-mandate]] §Attempt angles (B); Known issue 3
Kind: D
Fidelity: exact -/
noncomputable def pvTrader (DP : DeductiveProcess) (ov : Overlay) : Trader where
  strat n := pvStrat DP ov n

/-- The past-view trader's day strategy, unfolded.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pvTrader_strat (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    (pvTrader DP ov).strat n = pvStrat DP ov n := rfl

/-- **The core states are FAF's generic MarketMaker recursion for the past-view trader.** The
pattern of `liaStates_eq_marketMakerStates`.
Source: [[bli-overlay-mandate]] §Attempt angles (B)
Kind: L
Fidelity: exact -/
theorem coreState_eq_marketMakerStates (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    coreState DP ov n = marketMakerStates (pvTrader DP ov) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hpast : corePast DP ov n =
          List.ofFn fun i : Fin n => marketMakerStates (pvTrader DP ov) i := by
        apply List.ext_getElem
        · simp [corePast]
        · intro i hi₁ hi₂
          simp only [corePast, List.getElem_ofFn]
          exact ih i (by simpa [corePast] using hi₁)
      rw [coreState_eq, marketMakerStates]
      change MarketMaker (pvStrat DP ov n) (corePast DP ov n) (marketMakerError n)
          (marketMakerError_pos n) =
        MarketMaker (pvStrat DP ov n)
          (List.ofFn fun i : Fin n => marketMakerStates (pvTrader DP ov) i)
          (marketMakerError n) (marketMakerError_pos n)
      rw [hpast]

/-- The market form of `coreState_eq_marketMakerStates`.
Source: [[bli-overlay-mandate]] §Attempt angles (B)
Kind: L
Fidelity: exact -/
theorem coreHistory_eq_marketMakerHistory (DP : DeductiveProcess) (ov : Overlay) :
    coreHistory DP ov = marketMakerHistory (pvTrader DP ov) := by
  funext n φ
  unfold coreHistory marketMakerHistory
  rw [coreState_eq_marketMakerStates]

/-- **The transfer identity.** On every day and in every world, the past-view strategy's value on
the core market equals the firm's day strategy's value on the **overlaid** market: the
substitution lemma (`Strategy.value_substPast`) turns the former into the firm's value on the past
view of the core market, and T1 identifies that with the overlaid market on every mentioned cell
(days `< n`: both read the overlaid table; day `n`: the overlaid quote is the core quote on the
mentioned set).
Source: [[bli-overlay-mandate]] §Attempt angles (B)
Kind: L
Fidelity: exact -/
theorem pvStrat_value_eq (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) (w : Sentence → ℝ) :
    (pvStrat DP ov n).value (coreHistory DP ov) w =
      (firmStrat DP ov n).value (overlayHistory DP ov) w := by
  unfold pvStrat
  rw [Strategy.value_substPast]
  apply Strategy.value_eq_of_eqOn_mentioned
  intro φ hφ k hk
  rcases lt_or_eq_of_le hk with hlt | rfl
  · rw [EF.pastView_of_lt hlt, quoteBelow_of_lt DP ov hlt]
    rfl
  · rw [EF.pastView_self]
    unfold coreHistory overlayHistory
    rw [overlayQuote_of_mentionedBy DP ov hφ]
    rfl

/-! ## T4: the overlaid recursion is exploited by no e.c. trader -/

/-- **T4, the day bound.** On every day `n`, in every p.c. world, the firm's day strategy on the
overlaid table has value at most `marketMakerError n` **on the overlaid history**: FAF's
`marketMaker_day_value_le` at the past-view trader, transported by `pvStrat_value_eq`.
Source: [[bli-overlay-mandate]] T4 (`overlay_firm_dayValue_le`); [[bli-program]] §3.3 (i)–(ii)
Kind: C
Fidelity: exact
Hyps: (a) — `marketMaker_day_value_le` is FAF's theorem, applied -/
theorem overlay_firm_dayValue_le (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) (v : PCWorld) :
    (TradingFirmAt DP (overlayQuote DP ov) n).value (overlayHistory DP ov) v.payout ≤
      (marketMakerError n : ℝ) := by
  rw [← firmStrat_eq, ← pvStrat_value_eq, coreHistory_eq_marketMakerHistory]
  exact marketMaker_day_value_le (pvTrader DP ov) n v

/-- **T4, the day bound, second derivation** through the customer's entry point
`dayValue_le_of_accepted_state_subst` at the accepted core state — no `marketMakerStates` in
sight; this is the route a customer with its own market maker takes.
Source: [[bli-overlay-mandate]] T4; §Lifecycle
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem overlay_firm_dayValue_le_via_accepted (DP : DeductiveProcess) (ov : Overlay) (n : ℕ)
    (v : PCWorld) :
    (firmStrat DP ov n).value (overlayHistory DP ov) v.payout ≤ (marketMakerError n : ℝ) :=
  dayValue_le_of_accepted_state_subst (firmStrat DP ov n) (quoteBelow DP ov n) (corePast DP ov n)
    (marketMakerError n) (coreState DP ov n) (coreState_accepts DP ov n) (overlayHistory DP ov)
    (fun φ _ k hk => by rw [overlayHistory_eq_quote_cast, quoteBelow_of_lt DP ov hk])
    (fun φ hφ => by rw [overlayHistory_eq_quote_cast, overlayQuote_of_mentionedBy DP ov hφ]) v

/-- The firm's net worth on the overlaid market equals the past-view trader's on the core market,
in every world on every day.
Source: [[bli-overlay-mandate]] §Attempt angles (B)
Kind: L
Fidelity: exact -/
theorem overlay_netWorth_eq (DP : DeductiveProcess) (ov : Overlay) (v : PCWorld) (n : ℕ) :
    (tradingFirmTrader DP (overlayQuote DP ov)).netWorth (overlayHistory DP ov) v n =
      (pvTrader DP ov).netWorth (marketMakerHistory (pvTrader DP ov)) v n := by
  unfold Trader.netWorth
  apply Finset.sum_congr rfl
  intro i _
  change (TradingFirmAt DP (overlayQuote DP ov) i).value (overlayHistory DP ov) v.payout =
    (pvStrat DP ov i).value (marketMakerHistory (pvTrader DP ov)) v.payout
  rw [← firmStrat_eq, ← pvStrat_value_eq, coreHistory_eq_marketMakerHistory]

/-- The plausible assessments coincide.
Source: [[bli-overlay-mandate]] §Attempt angles (B)
Kind: L
Fidelity: exact -/
theorem overlay_plausibleAssessments_eq (DP : DeductiveProcess) (ov : Overlay) :
    (tradingFirmTrader DP (overlayQuote DP ov)).plausibleAssessments (overlayHistory DP ov) DP =
      (pvTrader DP ov).plausibleAssessments (marketMakerHistory (pvTrader DP ov)) DP := by
  unfold Trader.plausibleAssessments
  ext x
  simp only [Set.mem_setOf_eq, overlay_netWorth_eq]

/-- **T4. The firm does not exploit the overlaid market**: FAF's `marketMaker_not_exploited` at the
past-view trader, transported by the equality of plausible assessments.
Source: [[bli-overlay-mandate]] T4 (`overlay_firm_not_exploited`); [[bli-program]] §3.3 (iii)
Kind: C
Fidelity: exact
Hyps: (a) — `marketMaker_not_exploited` is FAF's theorem, applied -/
theorem overlay_firm_not_exploited (DP : DeductiveProcess) (ov : Overlay) :
    ¬ (tradingFirmTrader DP (overlayQuote DP ov)).Exploits (overlayHistory DP ov) DP := by
  intro h
  apply marketMaker_not_exploited (pvTrader DP ov) DP
  unfold Trader.Exploits at h ⊢
  rwa [overlay_plausibleAssessments_eq] at h

/-- **T4, second derivation**: the waived-days lemma T3(a) with `W = ∅` at the day bound.
Source: [[bli-overlay-mandate]] T4; T3(a) witness
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem overlay_firm_not_exploited_via_waived (DP : DeductiveProcess) (ov : Overlay) :
    ¬ (tradingFirmTrader DP (overlayQuote DP ov)).Exploits (overlayHistory DP ov) DP :=
  not_exploits_of_dayValue_le_off_finite (tradingFirmTrader DP (overlayQuote DP ov))
    (overlayHistory DP ov) DP (overlayHistory_range DP ov) ∅
    (fun n _ v => overlay_firm_dayValue_le DP ov n v)

/-- **T4 (L6(a)). The overlaid recursion is exploited by no efficiently computable trader**, for
every deductive process and every overlay: `trading_firm_dominance` on the exactly-rational `[0,1]`
table `overlayQuote DP ov` reduces any e.c. exploiter to the static firm
`tradingFirmTrader DP (overlayQuote DP ov)`, which is the firm the recursion ran (`firmStrat_eq`)
and which does not exploit (`overlay_firm_not_exploited`).
Source: [[bli-program]] §3.3 (i)–(iii), §4 row L6(a); [[bli-overlay-mandate]] T4
Kind: C
Fidelity: exact
Hyps: (a) — `trading_firm_dominance`, `marketMaker_not_exploited`, `MarketMaker_accepts` are FAF theorems, applied; `ov.range` is a field of D2 -/
theorem overlay_no_ec_trader_exploits (DP : DeductiveProcess) (ov : Overlay) (Tr : Trader)
    (hTr : EfficientlyComputable Tr) : ¬ Tr.Exploits (overlayHistory DP ov) DP := by
  intro hEx
  exact overlay_firm_not_exploited DP ov
    (trading_firm_dominance DP (overlayHistory DP ov) (overlayHistory_range DP ov)
      (overlayQuote DP ov) (overlayHistory_eq_quote_cast DP ov) Tr hTr hEx)

/-- **Assembly lemma (Kind L).** The criterion's semantic half is discharged by T4; the market's
computability is **assumed** here, not proved (L6(b), the stretch target T6). This is not L6 and
its ledger row is `partial: computability open` until T6 discharges `hmarket`.
Source: [[bli-overlay-mandate]] T4 (`overlay_isLogicalInductor_of_computableMarket`); mirrors FAF's `lia_isLogicalInductor_of_computableMarket`
Kind: L
Fidelity: weaker: `ComputableMarket (overlayHistory DP ov)` is a hypothesis
Hyps: (a) `hDP`, `hmarket` are hypotheses of the assembly, disclosed; not (c) — nothing is substituted, the market computability is simply not proved -/
theorem overlay_isLogicalInductor_of_computableMarket (DP : DeductiveProcess) (ov : Overlay)
    (hDP : ComputableDeductiveProcess DP) (hmarket : ComputableMarket (overlayHistory DP ov)) :
    IsLogicalInductor (overlayHistory DP ov) DP where
  marketComputable := hmarket
  processComputable := hDP
  noExploit := overlay_no_ec_trader_exploits DP ov

/-! ## T4 (v): with the zero overlay the recursion is FAF's LIA -/

/-- FAF's `liaStates`, unfolded to `MarketMaker` at the firm on the rational history of the prefix.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma liaStates_eq_MM (DP : DeductiveProcess) (n : ℕ) :
    liaStates DP n =
      MarketMaker (TradingFirmAt DP (rationalHistory (List.ofFn fun i : Fin n => liaStates DP i)) n)
        (List.ofFn fun i : Fin n => liaStates DP i) (marketMakerError n) (marketMakerError_pos n) := by
  rw [liaStates]
  rfl

/-- **The sanity identity, both halves by strong induction**: with the zero overlay the core states
are FAF's `liaStates` and the overlaid table is `liaQuote`. The strategies differ (`pvStrat` is
the substituted firm; FAF runs the bare firm on the prefix) but they are accepted against the same
past for the same candidates (`marketMakerAccepts_substPast_iff`), so `MarketMaker_congr` gives the
same state; off the mentioned set both tables quote `0` (the LIA state's support is inside the
firm's support).
Source: [[bli-overlay-mandate]] T4 (v)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem overlay_zero_eq_lia (DP : DeductiveProcess) (n : ℕ) :
    coreState DP Overlay.zero n = liaStates DP n ∧
      ∀ φ, overlayQuote DP Overlay.zero n φ = liaQuote DP n φ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hpast : corePast DP Overlay.zero n = List.ofFn fun i : Fin n => liaStates DP i := by
        apply List.ext_getElem
        · simp [corePast]
        · intro i hi₁ hi₂
          simp only [corePast, List.getElem_ofFn]
          exact (ih i (by simpa [corePast] using hi₁)).1
      have hQ : ∀ k < n, ∀ φ, quoteBelow DP Overlay.zero n k φ =
          rationalHistory (List.ofFn fun i : Fin n => liaStates DP i) k φ := by
        intro k hk φ
        rw [quoteBelow_of_lt DP Overlay.zero hk, (ih k hk).2, rationalHistory_liaPast DP hk]
      have hfirm : firmStrat DP Overlay.zero n =
          TradingFirmAt DP (rationalHistory (List.ofFn fun i : Fin n => liaStates DP i)) n := by
        unfold firmStrat
        apply TradingFirmAt_eq_of_eq_prefix
        intro day hday φ
        exact hQ day hday φ
      have hstate : coreState DP Overlay.zero n = liaStates DP n := by
        rw [coreState_eq, liaStates_eq_MM, ← hfirm, ← hpast]
        unfold pvStrat
        apply MarketMaker_congr
        intro B
        apply marketMakerAccepts_substPast_iff
        intro φ _ k hk
        rw [hQ k hk φ, hpast]
      refine ⟨hstate, fun φ => ?_⟩
      rw [overlayQuote_eq]
      split_ifs with hmem
      · rw [hstate]
        rfl
      · show (0 : ℚ) = liaQuote DP n φ
        unfold liaQuote
        rw [liaStates_eq_MM]
        symm
        apply RationalBeliefState.quote_eq_zero_of_not_mem
        intro hsupp
        have hacc := MarketMaker_accepts
          (TradingFirmAt DP (rationalHistory (List.ofFn fun i : Fin n => liaStates DP i)) n)
          (List.ofFn fun i : Fin n => liaStates DP i) (marketMakerError n) (marketMakerError_pos n)
        have h1 := hacc.1 hsupp
        rw [← hfirm] at h1
        exact hmem (support_subset_mentionedSet _ h1)

/-- With the zero overlay the core states are FAF's `liaStates`.
Source: [[bli-overlay-mandate]] T4 (v)
Kind: P
Fidelity: exact -/
theorem overlay_zero_coreState_eq_liaStates (DP : DeductiveProcess) (n : ℕ) :
    coreState DP Overlay.zero n = liaStates DP n :=
  (overlay_zero_eq_lia DP n).1

/-- **T4 (v). The sanity identity**: with the zero overlay the overlaid table **is** FAF's LIA
quote table — the construction is the right object, not a relabelling.
Source: [[bli-overlay-mandate]] T4 (v) (`overlayQuote_zero_eq_liaQuote`)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem overlayQuote_zero_eq_liaQuote (DP : DeductiveProcess) :
    overlayQuote DP Overlay.zero = liaQuote DP := by
  funext n φ
  exact (overlay_zero_eq_lia DP n).2 φ

/-- The market form of the sanity identity.
Source: [[bli-overlay-mandate]] T4 (v)
Kind: P
Fidelity: exact -/
theorem overlayHistory_zero_eq_liaHistory (DP : DeductiveProcess) :
    overlayHistory DP Overlay.zero = liaHistory DP := by
  funext n φ
  rw [overlayHistory_eq_quote_cast, liaHistory_eq_quote_cast, overlayQuote_zero_eq_liaQuote]

end Cleanroom.Bli.BliOverlay.AttemptB
