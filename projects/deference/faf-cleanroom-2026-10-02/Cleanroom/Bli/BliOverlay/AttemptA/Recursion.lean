import Cleanroom.Bli.BliOverlay.AttemptA.Waived
import LogicalInduction.Construction.LIA

/-!
# `bli-overlay` (attempt A) · Recursion: overlays, the overlaid market-maker recursion, and L6(a)

**The construction-facing file (D2, D3, T4), kept separate on purpose** (plan §0.5).

* **D2 `Overlay`** — a function of *finite* data: the day `n`, the list of the days-`< n` core
  states, the day-`n` core state, and the sentence, returning a rational price; the range
  condition `[0,1]` is a structure field, never a clamp. `Overlay.zero` and `Overlay.half` are
  the two instances used below and in `Witness.lean`.
* **D3, the recursion (angle A: the restricted past).** Day `n` produces a `DayRecord`: the
  **core state** and the **overlaid day-`n` quote table**. The firm's day-`n` strategy
  `dayStrat` is `TradingFirmAt DP (prevTable …) n`, built from the overlaid table of the days
  `< n` (`prevTable`, `0` on days `≥ n` — irrelevant, by `TradingFirmAt_eq_of_eq_prefix`). FAF's
  `MarketMaker` is then run against `dayStrat` and the **restricted past** `dayPast`: for each
  `k < n`, the finite state whose entries are `(φ, overlaid quote of day k at φ)` for
  `φ ∈ mentionedSet dayStrat` (`restrictState`, `restrictedPast`). The day-`n` overlaid quote is
  the core quote on the mentioned set and `ov` elsewhere. The recursion itself is
  `dayRec DP ov n = dayStep DP ov n (fun i : Fin n => dayRec DP ov i)` (well-founded on the day),
  and the definitions of record are read off it: `coreState`, `overlayQuote`, `overlayHistory`,
  `corePast`, and **`firmStrat DP ov n := TradingFirmAt DP (overlayQuote DP ov) n`** — the
  strategy the static firm `tradingFirmTrader DP (overlayQuote DP ov)` plays, so that
  `trading_firm_dominance` applies to *this* firm (`firmStrat_eq`; the concrete form of the
  wrong-market guard). `dayStrat_eq_firmStrat` ties the recursion's strategy to it, and
  `coreState_eq` exposes the day-`n` core state as `MarketMaker (firmStrat n) (restricted
  overlaid past) …`.
* **T4 (L6(a)).** `overlay_firm_dayValue_le`: the firm's day-`n` value on the **overlaid**
  history is `≤ 2^{-(n+1)}` in every p.c. world — from `MarketMaker_accepts` on the core state
  and the acceptance bridge `dayValue_le_of_accepts`, whose agreement hypothesis is discharged on
  days `< n` by the restriction (`rationalHistory_restrictedPast`) and on day `n` by
  `overlayQuote_of_mem`. Then `overlay_firm_not_exploited` (T3(a) with `W = ∅`) and the
  headline **`overlay_no_ec_trader_exploits`** (`trading_firm_dominance`). The assembly lemma
  `overlay_isLogicalInductor_of_computableMarket` takes `ComputableMarket` as a hypothesis and is
  `L`: nothing here claims computability (T6 is separate).
* **The sanity identity** `overlayQuote_zero_eq_liaQuote`: with the zero overlay the recursion
  *is* FAF's LIA — the core states are `liaStates`, through `MarketMaker_eq_of_eqOn_mentioned`
  (two pasts agreeing on every mentioned cell give the same `Nat.find`), and the un-mentioned
  sentences quote `0` in both. This is the check that the construction is the right object and
  not a relabelling.

Sources: [[bli-overlay-mandate]] D2, D3, T4 and traps (i)–(v); [[bli-program]] §3.3 (i)–(iii),
§4 row L6(a), §7 items 3, 8.
-/

namespace Cleanroom.Bli.BliOverlay.AttemptA

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

noncomputable section

/-! ## D2: overlays -/

/-- **D2. An overlay**: the price written on an unmentioned sentence on day `n`, as a function
of the day, the days-`< n` core states, the day-`n` core state and the sentence — finite data,
so that T6 is statable. The `[0,1]` range is a field, not a clamp (a clamp would silently alter
a customer's values).
Source: [[bli-overlay-mandate]] D2
Kind: D
Fidelity: exact -/
structure Overlay where
  /-- The overlay value. -/
  val : ℕ → List RationalBeliefState → RationalBeliefState → Sentence → ℚ
  /-- The `def:market` range clause, carried as data. -/
  range : ∀ n past B φ, 0 ≤ val n past B φ ∧ val n past B φ ≤ 1

/-- The zero overlay: every unmentioned sentence is priced `0`, as FAF's LIA does.
Source: [[bli-overlay-mandate]] T4(v)
Kind: D
Fidelity: exact -/
def Overlay.zero : Overlay :=
  ⟨fun _ _ _ _ => 0, fun _ _ _ _ => ⟨le_rfl, zero_le_one⟩⟩

/-- The constant-`1/2` overlay of the witness T5.
Source: [[bli-overlay-mandate]] T5
Kind: D
Fidelity: exact -/
def Overlay.half : Overlay :=
  ⟨fun _ _ _ _ => 1 / 2, fun _ _ _ _ => by norm_num⟩

/-! ## The restricted past -/

/-- Lookup in the association list `l.map (ψ ↦ (ψ, f ψ))` returns `f φ` for `φ ∈ l` (`l` without
duplicates). FAF proves this as the `private` `quoteFromEntries_map_eq` (`MarketMaker.lean`);
re-proved here — an FAF API request.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma quoteFromEntries_map_eq {l : List Sentence} (hl : l.Nodup) (f : Sentence → ℚ)
    {φ : Sentence} (hφ : φ ∈ l) :
    quoteFromEntries (l.map fun ψ => (ψ, f ψ)) φ = f φ := by
  induction l with
  | nil => simp at hφ
  | cons ψ rest ih =>
      simp only [List.nodup_cons] at hl
      simp only [List.mem_cons] at hφ
      rcases hφ with rfl | hφ
      · simp
      · have hne : φ ≠ ψ := fun h => hl.1 (h ▸ hφ)
        simp [hne, ih hl.2 hφ]

/-- The finite state listing `(φ, q φ)` for `φ ∈ S`: the restriction of a `[0,1]` table to a
finite set of sentences, as a `RationalBeliefState`. The range proof is a hypothesis, not a
clamp (trap (v)).
Source: [[bli-overlay-mandate]] § Attempt angles (A)
Kind: D
Fidelity: exact -/
def restrictState (S : Finset Sentence) (q : Sentence → ℚ) (hq : ∀ φ, 0 ≤ q φ ∧ q φ ≤ 1) :
    RationalBeliefState where
  entries := S.toList.map fun φ => (φ, q φ)
  keys_nodup := by
    rw [List.map_map]
    simpa [Function.comp_def] using S.nodup_toList
  bounded := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨φ, _, rfl⟩ := hp
    exact hq φ

/-- On `S`, the restricted state quotes the table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma restrictState_quote_of_mem {S : Finset Sentence} {q : Sentence → ℚ}
    {hq : ∀ φ, 0 ≤ q φ ∧ q φ ≤ 1} {φ : Sentence} (hφ : φ ∈ S) :
    (restrictState S q hq).quote φ = q φ := by
  unfold restrictState RationalBeliefState.quote
  exact quoteFromEntries_map_eq S.nodup_toList q (Finset.mem_toList.mpr hφ)

/-- The restricted past: for each `k < n`, the day-`k` table restricted to `S`.
Source: [[bli-overlay-mandate]] § Attempt angles (A)
Kind: D
Fidelity: exact -/
def restrictedPast (S : Finset Sentence) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ k φ, 0 ≤ Q k φ ∧ Q k φ ≤ 1) (n : ℕ) : List RationalBeliefState :=
  List.ofFn fun i : Fin n => restrictState S (Q i) (hQ i)

/-- On days `< n` and sentences of `S`, the rational history of the restricted past is the
table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma rationalHistory_restrictedPast {S : Finset Sentence} {Q : ℕ → Sentence → ℚ}
    {hQ : ∀ k φ, 0 ≤ Q k φ ∧ Q k φ ≤ 1} {n k : ℕ} (hk : k < n) {φ : Sentence} (hφ : φ ∈ S) :
    rationalHistory (restrictedPast S Q hQ n) k φ = Q k φ := by
  have hlen : k < (restrictedPast S Q hQ n).length := by simp [restrictedPast, hk]
  rw [rationalHistory_getElem _ hlen]
  simp only [restrictedPast, List.getElem_ofFn]
  exact restrictState_quote_of_mem hφ

/-- The restricted past reads the table only on days `< n` and sentences of `S`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma restrictedPast_congr {S : Finset Sentence} {Q Q' : ℕ → Sentence → ℚ}
    {hQ : ∀ k φ, 0 ≤ Q k φ ∧ Q k φ ≤ 1} {hQ' : ∀ k φ, 0 ≤ Q' k φ ∧ Q' k φ ≤ 1} {n : ℕ}
    (h : ∀ k < n, ∀ φ ∈ S, Q k φ = Q' k φ) :
    restrictedPast S Q hQ n = restrictedPast S Q' hQ' n := by
  unfold restrictedPast
  congr 1
  funext i
  apply RationalBeliefState.ext
  unfold restrictState
  simp only
  apply List.map_congr_left
  intro φ hφ
  rw [h i i.isLt φ (Finset.mem_toList.mp hφ)]

/-! ## D3: the recursion -/

/-- One day of the overlaid recursion: the core state and the overlaid day quote table (with
its range).
Source: [[bli-overlay-mandate]] D3
Kind: D
Fidelity: exact -/
structure DayRecord where
  /-- The day's core state (the market maker's output). -/
  core : RationalBeliefState
  /-- The day's overlaid quote table. -/
  quote : Sentence → ℚ
  /-- Its range. -/
  range : ∀ φ, 0 ≤ quote φ ∧ quote φ ≤ 1

/-- The overlaid table of the days `< n`, read off the previous records (`0` on days `≥ n`,
which the day-`n` firm never reads).
Source: [[bli-overlay-mandate]] D3
Kind: D
Fidelity: exact -/
def prevTable (n : ℕ) (prev : Fin n → DayRecord) : ℕ → Sentence → ℚ :=
  fun k φ => if h : k < n then (prev ⟨k, h⟩).quote φ else 0

/-- `prevTable` is in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prevTable_range (n : ℕ) (prev : Fin n → DayRecord) :
    ∀ k φ, 0 ≤ prevTable n prev k φ ∧ prevTable n prev k φ ≤ 1 := by
  intro k φ
  unfold prevTable
  split
  · exact (prev _).range φ
  · exact ⟨le_rfl, zero_le_one⟩

/-- `prevTable` on a day `< n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prevTable_of_lt (n : ℕ) (prev : Fin n → DayRecord) {k : ℕ} (hk : k < n) (φ : Sentence) :
    prevTable n prev k φ = (prev ⟨k, hk⟩).quote φ := by
  simp [prevTable, hk]

/-- The day-`n` firm strategy of the recursion: the trading firm **built from the overlaid
table** of the days `< n`.
Source: [[bli-overlay-mandate]] D3
Kind: D
Fidelity: exact -/
def dayStrat (DP : DeductiveProcess) (n : ℕ) (prev : Fin n → DayRecord) : Strategy n :=
  TradingFirmAt DP (prevTable n prev) n

/-- The restricted overlaid past fed to `MarketMaker` on day `n` (angle A).
Source: [[bli-overlay-mandate]] § Attempt angles (A)
Kind: D
Fidelity: exact -/
def dayPast (DP : DeductiveProcess) (n : ℕ) (prev : Fin n → DayRecord) :
    List RationalBeliefState :=
  restrictedPast (mentionedSet (dayStrat DP n prev)) (prevTable n prev) (prevTable_range n prev) n

/-- The day-`n` core state: FAF's `MarketMaker` against the firm built from the overlaid past,
checked against the restricted overlaid past.
Source: [[bli-overlay-mandate]] D3
Kind: D
Fidelity: exact -/
def dayCore (DP : DeductiveProcess) (n : ℕ) (prev : Fin n → DayRecord) : RationalBeliefState :=
  MarketMaker (dayStrat DP n prev) (dayPast DP n prev) (marketMakerError n) (marketMakerError_pos n)

/-- One step of the recursion: the core state, and the overlaid quote (core quote on the
mentioned set, `ov` elsewhere).
Source: [[bli-overlay-mandate]] D3
Kind: D
Fidelity: exact -/
def dayStep (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) (prev : Fin n → DayRecord) :
    DayRecord where
  core := dayCore DP n prev
  quote φ := if φ ∈ mentionedSet (dayStrat DP n prev) then (dayCore DP n prev).quote φ
    else ov.val n (List.ofFn fun i => (prev i).core) (dayCore DP n prev) φ
  range φ := by
    by_cases h : φ ∈ mentionedSet (dayStrat DP n prev)
    · rw [if_pos h]
      exact (dayCore DP n prev).quote_mem_Icc φ
    · rw [if_neg h]
      exact ov.range _ _ _ _

/-- **D3. The overlaid recursion** (well-founded on the day).
Source: [[bli-overlay-mandate]] D3; [[bli-program]] §3.3 (ii)
Kind: D
Fidelity: exact -/
def dayRec (DP : DeductiveProcess) (ov : Overlay) : ℕ → DayRecord
  | n => dayStep DP ov n (fun i : Fin n => dayRec DP ov i)
termination_by n => n
decreasing_by exact i.isLt

/-- **The core state** of day `n`.
Source: [[bli-overlay-mandate]] D3
Kind: D
Fidelity: exact -/
def coreState (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) : RationalBeliefState :=
  (dayRec DP ov n).core

/-- **The overlaid table**: the core quote on the day's mentioned set, the overlay elsewhere.
Source: [[bli-overlay-mandate]] D3
Kind: D
Fidelity: exact -/
def overlayQuote (DP : DeductiveProcess) (ov : Overlay) : ℕ → Sentence → ℚ :=
  fun n φ => (dayRec DP ov n).quote φ

/-- **The overlaid market**: the real history obtained by casting `overlayQuote`.
Source: [[bli-overlay-mandate]] D3
Kind: D
Fidelity: exact -/
def overlayHistory (DP : DeductiveProcess) (ov : Overlay) : History :=
  fun n φ => (overlayQuote DP ov n φ : ℝ)

/-- The list of the days-`< n` core states (the overlay's second argument).
Source: [[bli-overlay-mandate]] D3
Kind: D
Fidelity: exact -/
def corePast (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) : List RationalBeliefState :=
  List.ofFn fun i : Fin n => coreState DP ov i

/-- **The firm's day-`n` strategy**: the trading firm built from the overlaid table — the
strategy the static firm `tradingFirmTrader DP (overlayQuote DP ov)` plays on day `n`.
Source: [[bli-overlay-mandate]] D3
Kind: D
Fidelity: exact -/
def firmStrat (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) : Strategy n :=
  TradingFirmAt DP (overlayQuote DP ov) n

/-- `overlayQuote` is in `[0,1]`.
Source: [[bli-overlay-mandate]] D3 (`overlayHistory_range`)
Kind: L
Fidelity: exact -/
lemma overlayQuote_range (DP : DeductiveProcess) (ov : Overlay) :
    ∀ k φ, 0 ≤ overlayQuote DP ov k φ ∧ overlayQuote DP ov k φ ≤ 1 :=
  fun k φ => (dayRec DP ov k).range φ

/-- The restricted overlaid past of day `n`, in terms of the definitions of record.
Source: [[bli-overlay-mandate]] § Attempt angles (A)
Kind: D
Fidelity: exact -/
def overlayRestrictedPast (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    List RationalBeliefState :=
  restrictedPast (mentionedSet (firmStrat DP ov n)) (overlayQuote DP ov) (overlayQuote_range DP ov) n

/-! ## The identities of D3 -/

/-- `overlayHistory_range`: the `def:market` range clause for the overlaid market, from
`RationalBeliefState.bounded` and `Overlay.range` (no clamp).
Source: [[bli-overlay-mandate]] D3
Kind: L
Fidelity: exact -/
lemma overlayHistory_range (DP : DeductiveProcess) (ov : Overlay) :
    ∀ day φ, 0 ≤ overlayHistory DP ov day φ ∧ overlayHistory DP ov day φ ≤ 1 := by
  intro d φ
  unfold overlayHistory
  exact ⟨by exact_mod_cast (overlayQuote_range DP ov d φ).1,
    by exact_mod_cast (overlayQuote_range DP ov d φ).2⟩

/-- `overlayHistory_eq_quote_cast`: the real market is the cast of the exact rational table.
Source: [[bli-overlay-mandate]] D3
Kind: L
Fidelity: exact -/
lemma overlayHistory_eq_quote_cast (DP : DeductiveProcess) (ov : Overlay) (day : ℕ)
    (φ : Sentence) : overlayHistory DP ov day φ = (overlayQuote DP ov day φ : ℝ) := rfl

/-- **`firmStrat_eq`**: the recursion's firm strategy is the day-`n` strategy of the static
complete-table firm on the overlaid table — the concrete wrong-market guard.
Source: [[bli-overlay-mandate]] D3; [[bli-program]] §7 item 3
Kind: L
Fidelity: exact -/
lemma firmStrat_eq (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    firmStrat DP ov n = (tradingFirmTrader DP (overlayQuote DP ov)).strat n := rfl

/-- The recursion's equation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma dayRec_unfold (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    dayRec DP ov n = dayStep DP ov n (fun i : Fin n => dayRec DP ov i) := by
  rw [dayRec]

/-- The previous-records table of the recursion is the overlaid table on days `< n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prevTable_dayRec (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) {k : ℕ} (hk : k < n)
    (φ : Sentence) :
    prevTable n (fun i : Fin n => dayRec DP ov i) k φ = overlayQuote DP ov k φ := by
  rw [prevTable_of_lt n _ hk]
  rfl

/-- **The recursion's day-`n` strategy is `firmStrat`**: the firm built from the previous
records' table equals the firm built from the whole overlaid table, because the firm reads only
days `< n` (`TradingFirmAt_eq_of_eq_prefix`).
Source: [[bli-overlay-mandate]] D3
Kind: L
Fidelity: exact -/
lemma dayStrat_eq_firmStrat (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    dayStrat DP n (fun i : Fin n => dayRec DP ov i) = firmStrat DP ov n := by
  unfold dayStrat firmStrat
  apply TradingFirmAt_eq_of_eq_prefix
  intro k hk φ
  exact prevTable_dayRec DP ov n hk φ

/-- The day-`n` record's core, unfolded one step.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma dayRec_core (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    (dayRec DP ov n).core = dayCore DP n (fun i : Fin n => dayRec DP ov i) := by
  rw [dayRec_unfold]
  rfl

/-- The day-`n` record's quote, unfolded one step.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma dayRec_quote (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) (φ : Sentence) :
    (dayRec DP ov n).quote φ =
      if φ ∈ mentionedSet (dayStrat DP n (fun i : Fin n => dayRec DP ov i)) then
        (dayCore DP n (fun i : Fin n => dayRec DP ov i)).quote φ
      else ov.val n (List.ofFn fun i : Fin n => (dayRec DP ov i).core)
        (dayCore DP n (fun i : Fin n => dayRec DP ov i)) φ := by
  conv_lhs => rw [dayRec_unfold]
  rfl

/-- **`coreState_eq`**: the day-`n` core state is FAF's `MarketMaker` against `firmStrat n`
and the restricted overlaid past.
Source: [[bli-overlay-mandate]] D3, § Attempt angles (A)
Kind: L
Fidelity: exact -/
lemma coreState_eq (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    coreState DP ov n = MarketMaker (firmStrat DP ov n) (overlayRestrictedPast DP ov n)
      (marketMakerError n) (marketMakerError_pos n) := by
  unfold coreState
  rw [dayRec_core]
  unfold dayCore dayPast
  rw [dayStrat_eq_firmStrat]
  unfold overlayRestrictedPast
  congr 1
  apply restrictedPast_congr
  intro k hk φ _
  exact prevTable_dayRec DP ov n hk φ

/-- **The core state is accepted** by the market maker against `firmStrat n` and the restricted
overlaid past (FAF's `MarketMaker_accepts`, applied).
Source: [[bli-overlay-mandate]] T4
Kind: L
Fidelity: exact -/
lemma coreState_accepts (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    MarketMakerAccepts (firmStrat DP ov n) (overlayRestrictedPast DP ov n) (marketMakerError n)
      (coreState DP ov n) := by
  rw [coreState_eq]
  exact MarketMaker_accepts _ _ _ _

/-- The overlaid quote, as a case split on the mentioned set.
Source: [[bli-overlay-mandate]] D3
Kind: L
Fidelity: exact -/
lemma overlayQuote_eq_ite (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) (φ : Sentence) :
    overlayQuote DP ov n φ =
      if φ ∈ mentionedSet (firmStrat DP ov n) then (coreState DP ov n).quote φ
      else ov.val n (corePast DP ov n) (coreState DP ov n) φ := by
  unfold overlayQuote
  rw [dayRec_quote, dayStrat_eq_firmStrat, ← dayRec_core]
  rfl

/-- **`overlayQuote_of_mem`**: on the mentioned set, the overlaid quote is the core quote.
Source: [[bli-overlay-mandate]] D3
Kind: L
Fidelity: exact -/
lemma overlayQuote_of_mem (DP : DeductiveProcess) (ov : Overlay) {n : ℕ} {φ : Sentence}
    (h : φ ∈ mentionedSet (firmStrat DP ov n)) :
    overlayQuote DP ov n φ = (coreState DP ov n).quote φ := by
  rw [overlayQuote_eq_ite, if_pos h]

/-- **`overlayQuote_of_not_mem`**: off the mentioned set, the overlaid quote is the overlay.
Source: [[bli-overlay-mandate]] D3
Kind: L
Fidelity: exact -/
lemma overlayQuote_of_not_mem (DP : DeductiveProcess) (ov : Overlay) {n : ℕ} {φ : Sentence}
    (h : φ ∉ mentionedSet (firmStrat DP ov n)) :
    overlayQuote DP ov n φ = ov.val n (corePast DP ov n) (coreState DP ov n) φ := by
  rw [overlayQuote_eq_ite, if_neg h]

/-! ## T4: the overlaid recursion is exploited by no e.c. trader -/

/-- **T4, the day bound.** The firm's day-`n` strategy has value at most `marketMakerError n` on
the **overlaid** history in every propositionally consistent world: the core state is accepted
against the restricted overlaid past, and that candidate history agrees with the overlaid history
on every mentioned cell — on days `< n` by the restriction, on day `n` because the overlaid quote
is the core quote on the mentioned set.
Source: [[bli-overlay-mandate]] T4; [[bli-program]] §3.3 (i)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem overlay_firm_dayValue_le (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    ∀ v : PCWorld,
      (firmStrat DP ov n).value (overlayHistory DP ov) v.payout ≤ (marketMakerError n : ℝ) := by
  apply dayValue_le_of_accepts (firmStrat DP ov n) (overlayRestrictedPast DP ov n)
    (marketMakerError n) (coreState DP ov n) (coreState_accepts DP ov n)
  intro φ hφ k hk
  rw [overlayHistory_eq_quote_cast]
  congr 1
  rcases Nat.lt_or_eq_of_le hk with hlt | rfl
  · rw [candidateRationalHistory, Function.update_of_ne (Nat.ne_of_lt hlt)]
    unfold overlayRestrictedPast
    exact (rationalHistory_restrictedPast hlt (mem_mentionedSet_iff.mpr hφ)).symm
  · rw [candidateRationalHistory, Function.update_self]
    exact overlayQuote_of_mem DP ov (mem_mentionedSet_iff.mpr hφ)

/-- **T4. The firm does not exploit the overlaid market**: T3(a) with `W = ∅`.
Source: [[bli-overlay-mandate]] T4; [[bli-program]] §3.3 (iii)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem overlay_firm_not_exploited (DP : DeductiveProcess) (ov : Overlay) :
    ¬ (tradingFirmTrader DP (overlayQuote DP ov)).Exploits (overlayHistory DP ov) DP :=
  not_exploits_of_dayValue_le_off_finite _ _ DP (overlayHistory_range DP ov) ∅
    (fun n _ v => overlay_firm_dayValue_le DP ov n v)

/-- **T4 (L6(a), headline). No efficiently computable trader exploits the overlaid market**, for
every process `DP` and every overlay `ov`: by FAF's `trading_firm_dominance` an exploiting e.c.
trader would make the static firm on the overlaid table exploit it, and the firm does not
(`overlay_firm_not_exploited`).
Source: [[bli-overlay-mandate]] T4; [[bli-program]] §3.3, §4 row L6(a)
Kind: C
Fidelity: exact
Hyps: (a) — `MarketMaker_accepts`, `trading_firm_dominance` are FAF theorems, applied;
`ov.range` is a field of D2 -/
theorem overlay_no_ec_trader_exploits (DP : DeductiveProcess) (ov : Overlay) (Tr : Trader)
    (hTr : EfficientlyComputable Tr) : ¬ Tr.Exploits (overlayHistory DP ov) DP := by
  intro hex
  have hfirm := trading_firm_dominance DP (overlayHistory DP ov) (overlayHistory_range DP ov)
    (overlayQuote DP ov) (overlayHistory_eq_quote_cast DP ov) Tr hTr hex
  exact overlay_firm_not_exploited DP ov hfirm

/-- **Assembly lemma (Kind L).** The overlaid market is a logical inductor **if** it is a
computable market — the computability is *assumed* here, exactly as in FAF's
`lia_isLogicalInductor_of_computableMarket`; nothing in this file establishes it (T6 is the
separate, stretch target). Its ledger row is `partial: computability open`.
Source: [[bli-overlay-mandate]] T4 (assembly); [[bli-program]] §7 item 8
Kind: L
Fidelity: weaker: `ComputableMarket (overlayHistory DP ov)` is a hypothesis, not proved
Hyps: (b) `hmarket : ComputableMarket (overlayHistory DP ov)` — assumed (L6(b), OPEN);
(a) `hDP` is the process's computability, the criterion's own hypothesis -/
theorem overlay_isLogicalInductor_of_computableMarket (DP : DeductiveProcess) (ov : Overlay)
    (hDP : ComputableDeductiveProcess DP) (hmarket : ComputableMarket (overlayHistory DP ov)) :
    IsLogicalInductor (overlayHistory DP ov) DP where
  marketComputable := hmarket
  processComputable := hDP
  noExploit := overlay_no_ec_trader_exploits DP ov

/-! ## The sanity identity: the zero overlay is FAF's LIA -/

/-- **`MarketMaker` congruence on mentioned cells.** Two pasts that agree, on every day `< n`, at
every sentence the strategy mentions, give the same market-maker output: the acceptance predicate
is the same for every candidate (T1), so the `Nat.find` is the same.
Source: [[bli-overlay-mandate]] T4(v)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem MarketMaker_eq_of_eqOn_mentioned {n : ℕ} (T : Strategy n)
    (past₁ past₂ : List RationalBeliefState) (ε : ℚ) (hε : 0 < ε)
    (h : ∀ φ, MentionedBy T φ → ∀ k < n, rationalHistory past₁ k φ = rationalHistory past₂ k φ) :
    MarketMaker T past₁ ε hε = MarketMaker T past₂ ε hε := by
  have hacc : ∀ B, MarketMakerAccepts T past₁ ε B ↔ MarketMakerAccepts T past₂ ε B := by
    intro B
    unfold MarketMakerAccepts
    have hval : ∀ b : ↥T.support → Bool,
        T.marketValueRat (candidateRationalHistory past₁ n B) (supportBitWorldRat T b) =
          T.marketValueRat (candidateRationalHistory past₂ n B) (supportBitWorldRat T b) := by
      intro b
      apply Strategy.marketValueRat_eq_of_eqOn_mentioned
      intro φ hφ k hk
      rcases Nat.lt_or_eq_of_le hk with hlt | rfl
      · simp only [candidateRationalHistory, Function.update_of_ne (Nat.ne_of_lt hlt)]
        exact h φ hφ k hlt
      · simp [candidateRationalHistory]
    simp only [hval]
  have hcand : ∀ k, MarketMakerCandidateAccepts T past₁ ε k ↔
      MarketMakerCandidateAccepts T past₂ ε k := by
    intro k
    unfold MarketMakerCandidateAccepts
    simp only [hacc]
  have hidx : marketMakerIndex T past₁ ε hε = marketMakerIndex T past₂ ε hε := by
    unfold marketMakerIndex
    exact Nat.find_congr' (fun {k} => hcand k)
  have h1 := MarketMaker_candidate T past₁ ε hε
  have h2 := MarketMaker_candidate T past₂ ε hε
  rw [hidx] at h1
  exact Option.some.inj (h1.symm.trans h2)

/-- FAF's `liaStates`, unfolded one step.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma liaStates_eq (DP : DeductiveProcess) (n : ℕ) :
    liaStates DP n = MarketMaker ((TradingFirm DP).action n (List.ofFn fun i : Fin n => liaStates DP i))
      (List.ofFn fun i : Fin n => liaStates DP i) (marketMakerError n) (marketMakerError_pos n) := by
  rw [liaStates]

/-- **The zero overlay is FAF's LIA**: `overlayQuote DP Overlay.zero = liaQuote DP`. The core
states are `liaStates` (strong induction: the firms agree by `TradingFirmAt_eq_of_eq_prefix`, the
market makers by `MarketMaker_eq_of_eqOn_mentioned`), and off the mentioned set both tables quote
`0` — the LIA state's support is inside the firm's support (`MarketMakerAccepts.1`), which is
inside the mentioned set. This is the artifact check that D3 is the right object.
Source: [[bli-overlay-mandate]] T4(v)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem overlayQuote_zero_eq_liaQuote (DP : DeductiveProcess) :
    overlayQuote DP Overlay.zero = liaQuote DP := by
  have key : ∀ n, coreState DP Overlay.zero n = liaStates DP n ∧
      ∀ φ, overlayQuote DP Overlay.zero n φ = liaQuote DP n φ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hfirm : firmStrat DP Overlay.zero n =
          (TradingFirm DP).action n (List.ofFn fun i : Fin n => liaStates DP i) := by
        unfold firmStrat
        show TradingFirmAt DP _ n = TradingFirmAt DP (rationalHistory _) n
        apply TradingFirmAt_eq_of_eq_prefix
        intro k hk φ
        rw [(ih k hk).2 φ, rationalHistory_liaPast DP hk]
      have hcore : coreState DP Overlay.zero n = liaStates DP n := by
        rw [coreState_eq, liaStates_eq, hfirm]
        apply MarketMaker_eq_of_eqOn_mentioned
        intro φ hφ k hk
        have hφ' : φ ∈ mentionedSet (firmStrat DP Overlay.zero n) := by
          rw [hfirm]
          exact mem_mentionedSet_iff.mpr hφ
        unfold overlayRestrictedPast
        rw [rationalHistory_restrictedPast hk hφ', (ih k hk).2 φ, rationalHistory_liaPast DP hk]
      refine ⟨hcore, fun φ => ?_⟩
      by_cases hφ : φ ∈ mentionedSet (firmStrat DP Overlay.zero n)
      · rw [overlayQuote_of_mem DP _ hφ, hcore]
        rfl
      · rw [overlayQuote_of_not_mem DP _ hφ]
        show (0 : ℚ) = liaQuote DP n φ
        symm
        unfold liaQuote
        apply RationalBeliefState.quote_eq_zero_of_not_mem
        intro hsupp
        apply hφ
        rw [hfirm]
        have hacc := MarketMaker_accepts
          ((TradingFirm DP).action n (List.ofFn fun i : Fin n => liaStates DP i))
          (List.ofFn fun i : Fin n => liaStates DP i) (marketMakerError n) (marketMakerError_pos n)
        rw [liaStates_eq] at hsupp
        exact support_subset_mentionedSet _ (hacc.1 hsupp)
  funext n φ
  exact (key n).2 φ

/-- With the zero overlay, the overlaid market is `liaHistory`.
Source: [[bli-overlay-mandate]] T4(v)
Kind: L
Fidelity: exact -/
theorem overlayHistory_zero_eq_liaHistory (DP : DeductiveProcess) :
    overlayHistory DP Overlay.zero = liaHistory DP := by
  funext n φ
  rw [overlayHistory_eq_quote_cast, liaHistory_eq_quote_cast, overlayQuote_zero_eq_liaQuote]

end

end Cleanroom.Bli.BliOverlay.AttemptA
