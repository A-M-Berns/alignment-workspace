/-
# An exactly compliant market for floor schedules

Round `projects/normativity/rounds/2026-11-10-exact-conditions-capital/`.

`ExactConditions` states its theorems over any `DualCertifiedMarket`.  This file builds
one for every **floor schedule** — one floor `c n ≤ price (φ n)` per day — and so
inhabits the interface with a nontrivial region and an explicit multiplier.

The construction reduces to the pinned market maker.  Reparametrize the day's prices by
`x = lo + (1 - lo) y`, with `lo` the floor on the floored sentence and `0` elsewhere.
Substituting that for the day's price features in the firm's strategy (`liftDay`) gives a
strategy the unmodified `MarketMaker` prices at some rational `y`; the prices `x` then
satisfy the floor exactly.  The market maker's guarantee at `y` says, sentence by
sentence, that a positive net position sits at price one and a negative one at the
reparametrized zero, which is the floor.  The multiplier on the floor is the size of the
negative position held there (`floor_day_le`); no projection and no linear-programming
duality is used.

* `liftDay`, `liftDay_denoteWith` — the substitution and its semantics.
* `floor_day_le` — the day inequality with its multipliers, for any `lo`.
* `FloorSchedule.market` — the dual-certified market of a floor schedule.
* `plainMarket` — the unconstrained market as a dual-certified market, all multipliers
  zero.
* Inhabitants of the hypothesis packages of `ExactConditions` and
  `ExactConditionsReserve`.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.ExactConditionsReserve

namespace Workspace.Normativity.Contrib.ExactConditions

open LogicalInduction
open Workspace.Normativity.Contrib.AssessmentProcess
open Workspace.Normativity.Contrib.AssessmentFirm
open Workspace.Normativity.Contrib.DeductiveRegion

/-! ## Lifting the day's prices -/

/-- Replace each day-`n` price feature `φ^{*n}` by `lo φ + (1 - lo φ) · φ^{*n}`. -/
def liftDay (n : ℕ) (lo : Sentence → ℚ) : EF → EF
  | .price φ m =>
      if m = n then .add (.const (lo φ)) (.mul (.const (1 - lo φ)) (.price φ m))
      else .price φ m
  | .const q => .const q
  | .add a b => .add (liftDay n lo a) (liftDay n lo b)
  | .mul a b => .mul (liftDay n lo a) (liftDay n lo b)
  | .max a b => .max (liftDay n lo a) (liftDay n lo b)
  | .safeRecip a => .safeRecip (liftDay n lo a)
  | .var i => .var i
  | .letE x body => .letE (liftDay n lo x) (liftDay n lo body)

lemma liftDay_rank (n : ℕ) (lo : Sentence → ℚ) (e : EF) : (liftDay n lo e).rank = e.rank := by
  induction e with
  | price φ m =>
      unfold liftDay
      split_ifs with h
      · change Nat.max 0 (Nat.max 0 m) = m
        simp
      · rfl
  | const q => rfl
  | add a b iha ihb => simp [liftDay, iha, ihb]
  | mul a b iha ihb => simp [liftDay, iha, ihb]
  | max a b iha ihb => simp [liftDay, iha, ihb]
  | safeRecip a iha => simp [liftDay, iha]
  | var i => rfl
  | letE x body ihx ihb =>
      change Nat.max (liftDay n lo x).rank (liftDay n lo body).rank = Nat.max x.rank body.rank
      rw [ihx, ihb]

/-- The history whose day-`n` prices are the lifted ones. -/
def liftHist (n : ℕ) (lo : Sentence → ℚ) (V : History) : History :=
  Function.update V n fun φ => (lo φ : ℝ) + (1 - (lo φ : ℝ)) * V n φ

lemma liftHist_self (n : ℕ) (lo : Sentence → ℚ) (V : History) (φ : Sentence) :
    liftHist n lo V n φ = (lo φ : ℝ) + (1 - (lo φ : ℝ)) * V n φ := by
  simp [liftHist]

lemma liftHist_of_ne (n : ℕ) (lo : Sentence → ℚ) (V : History) {m : ℕ} (h : m ≠ n) :
    liftHist n lo V m = V m := by
  simp [liftHist, Function.update_of_ne h]

lemma liftDay_denoteWith (n : ℕ) (lo : Sentence → ℚ) (e : EF) (ρ : List ℝ) (V : History) :
    (liftDay n lo e).denoteWith ρ V = e.denoteWith ρ (liftHist n lo V) := by
  induction e generalizing ρ with
  | price φ m =>
      unfold liftDay
      split_ifs with h
      · subst h
        simp [liftHist_self]
      · simp [liftHist_of_ne n lo V h]
  | const q => simp [liftDay]
  | add a b iha ihb => simp [liftDay, iha, ihb]
  | mul a b iha ihb => simp [liftDay, iha, ihb]
  | max a b iha ihb => simp [liftDay, iha, ihb]
  | safeRecip a iha => simp [liftDay, iha]
  | var i => simp [liftDay]
  | letE x body ihx ihb => simp [liftDay, ihx, ihb]

lemma liftDay_denote (n : ℕ) (lo : Sentence → ℚ) (e : EF) (V : History) :
    (liftDay n lo e).denote V = e.denote (liftHist n lo V) :=
  liftDay_denoteWith n lo e [] V

/-- A strategy with its day-`n` price features lifted. -/
def liftStrategy (n : ℕ) (lo : Sentence → ℚ) (T : Strategy n) : Strategy n where
  trades := T.trades.map fun p => (liftDay n lo p.1, p.2)
  rank_le := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [liftDay_rank]
    exact T.rank_le q hq

lemma liftStrategy_support (n : ℕ) (lo : Sentence → ℚ) (T : Strategy n) :
    (liftStrategy n lo T).support = T.support := by
  ext φ
  simp only [Strategy.support, liftStrategy, Finset.mem_image, List.mem_toFinset,
    List.mem_map]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨_, ⟨q, hq, rfl⟩, rfl⟩

/-! ## Aggregate positions, in list form -/

open Classical in
lemma shares_eq_list {n : ℕ} (T : Strategy n) (V : History) (φ : Sentence) :
    T.shares V φ = (T.trades.map fun t => if t.2 = φ then t.1.denote V else 0).sum := by
  unfold Strategy.shares
  rw [Finset.sum_filter]
  convert Fin.sum_univ_fun_getElem T.trades
    (fun t => if t.2 = φ then t.1.denote V else 0) using 2
  rfl

lemma liftStrategy_shares (n : ℕ) (lo : Sentence → ℚ) (T : Strategy n) (V : History)
    (φ : Sentence) :
    (liftStrategy n lo T).shares V φ = T.shares (liftHist n lo V) φ := by
  rw [shares_eq_list, shares_eq_list]
  simp only [liftStrategy, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, liftDay_denote]

lemma shares_eq_zero_of_not_mem {n : ℕ} (T : Strategy n) (V : History) {φ : Sentence}
    (hφ : φ ∉ T.support) : T.shares V φ = 0 := by
  rw [shares_eq_list]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  rw [if_neg]
  intro h
  exact hφ (h ▸ T.snd_mem_support ht)

lemma shares_eq_of_eqUpTo {n : ℕ} (T : Strategy n) (V W : History)
    (hVW : ∀ day, day ≤ n → ∀ φ, V day φ = W day φ) (φ : Sentence) :
    T.shares V φ = T.shares W φ := by
  rw [shares_eq_list, shares_eq_list]
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [t.1.denote_eq_of_eqUpTo V W n (T.rank_le t ht) hVW]

/-! ## The day inequality -/

/-- One sentence's contribution.  A position `s` at the lifted price `c + (1 - c) p`,
plus the multiplier `max 0 (-s)` on the floor `w - c`, is at most the position's value at
the unlifted price `p` against the vertex its sign selects. -/
lemma floor_term_le (s w p c : ℝ) (hw : 0 ≤ w ∧ w ≤ 1) (hp : 0 ≤ p ∧ p ≤ 1)
    (hc : 0 ≤ c ∧ c ≤ 1) :
    s * (w - (c + (1 - c) * p)) + max 0 (-s) * (w - c) ≤
      s * ((if 0 < s then 1 else 0) - p) := by
  by_cases hs : 0 < s
  · rw [if_pos hs, max_eq_left (by linarith), zero_mul, add_zero]
    apply mul_le_mul_of_nonneg_left _ hs.le
    nlinarith [mul_nonneg hc.1 (sub_nonneg.mpr hp.2)]
  · rw [if_neg hs, max_eq_right (by linarith)]
    have h : 0 ≤ -s := by linarith
    nlinarith [mul_nonneg (mul_nonneg h hc.1) hp.1]

/-- **The day inequality with its multipliers.**  If the lifted strategy is accepted at
the valuation `V'` — its value at every Boolean table on its support is at most `ε` —
then at the lifted prices the original strategy's value at any cube valuation `w`, plus
the multiplier `max 0 (-position)` on each floor `w φ - lo φ`, is at most `ε`. -/
theorem floor_day_le {n : ℕ} (T : Strategy n) (prior : History) (lo : Sentence → ℚ)
    (hlo : ∀ φ, 0 ≤ lo φ ∧ lo φ ≤ 1) (V' : Valuation) (hV' : ∀ φ, 0 ≤ V' φ ∧ V' φ ≤ 1)
    (ε : ℝ)
    (hacc : ∀ b : ↥(liftStrategy n lo T).support → Bool,
      (liftStrategy n lo T).value (Function.update prior n V')
        (supportBitWorld (liftStrategy n lo T) b) ≤ ε)
    (w : Sentence → ℝ) (hw : ∀ φ, 0 ≤ w φ ∧ w φ ≤ 1) :
    T.value (liftHist n lo (Function.update prior n V')) w +
      ∑ φ ∈ T.support,
        max 0 (-(T.shares (liftHist n lo (Function.update prior n V')) φ)) *
          (w φ - (lo φ : ℝ)) ≤ ε := by
  classical
  have hHn : ∀ φ, liftHist n lo (Function.update prior n V') n φ =
      (lo φ : ℝ) + (1 - (lo φ : ℝ)) * V' φ := by
    intro φ
    rw [liftHist_self, Function.update_self]
  have h := hacc fun ψ =>
    decide (0 < T.shares (liftHist n lo (Function.update prior n V')) ψ.1)
  rw [Strategy.value_eq_sum_support,
    Finset.sum_congr (liftStrategy_support n lo T) (fun _ _ => rfl)] at h
  rw [Strategy.value_eq_sum_support, ← Finset.sum_add_distrib]
  refine le_trans (Finset.sum_le_sum fun φ hφ => ?_) h
  have hφ' : φ ∈ (liftStrategy n lo T).support := by rwa [liftStrategy_support]
  rw [liftStrategy_shares, hHn, Function.update_self]
  have hbit : supportBitWorld (liftStrategy n lo T) (fun ψ =>
      decide (0 < T.shares (liftHist n lo (Function.update prior n V')) ψ.1)) φ =
      if 0 < T.shares (liftHist n lo (Function.update prior n V')) φ then 1 else 0 := by
    unfold supportBitWorld
    rw [dif_pos hφ']
    simp
  rw [hbit]
  exact floor_term_le _ _ _ _ (hw φ) (hV' φ)
    ⟨by exact_mod_cast (hlo φ).1, by exact_mod_cast (hlo φ).2⟩

/-- Without lifting: a strategy whose value at every Boolean table on its support is at
most `ε` has value at most `ε` at every cube valuation. -/
theorem value_le_of_bitTables {n : ℕ} (T : Strategy n) (V : History) (ε : ℝ)
    (hacc : ∀ b : ↥T.support → Bool, T.value V (supportBitWorld T b) ≤ ε)
    (w : Sentence → ℝ) (hw : ∀ φ, 0 ≤ w φ ∧ w φ ≤ 1) : T.value V w ≤ ε := by
  classical
  have h := hacc fun ψ => decide (0 < T.shares V ψ.1)
  rw [Strategy.value_eq_sum_support] at h ⊢
  refine le_trans (Finset.sum_le_sum fun φ hφ => ?_) h
  have hbit : supportBitWorld T (fun ψ => decide (0 < T.shares V ψ.1)) φ =
      if 0 < T.shares V φ then 1 else 0 := by
    unfold supportBitWorld
    rw [dif_pos hφ]
    simp
  rw [hbit]
  by_cases hs : 0 < T.shares V φ
  · rw [if_pos hs]
    exact mul_le_mul_of_nonneg_left (by linarith [(hw φ).2]) hs.le
  · rw [if_neg hs]
    exact mul_le_mul_of_nonpos_left (by linarith [(hw φ).1]) (not_lt.mp hs)

/-! ## The floored belief state -/

lemma quoteFromEntries_filter_ne (l : List (Sentence × ℚ)) (ψ φ : Sentence) (h : φ ≠ ψ) :
    quoteFromEntries (l.filter fun p => p.1 ≠ ψ) φ = quoteFromEntries l φ := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨a, q⟩ := p
      by_cases hp : a = ψ
      · subst hp
        rw [List.filter_cons_of_neg (by simp), quoteFromEntries_cons, if_neg h, ih]
      · rw [List.filter_cons_of_pos (by simpa using hp), quoteFromEntries_cons,
          quoteFromEntries_cons, ih]

/-- The belief state quoting `c + (1 - c) q` at `ψ`, where `q` is `B'`'s quote there, and
`B'`'s quote elsewhere. -/
def floorState (ψ : Sentence) (c : ℚ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (B' : RationalBeliefState) : RationalBeliefState where
  entries := (ψ, c + (1 - c) * B'.quote ψ) :: B'.entries.filter fun p => p.1 ≠ ψ
  keys_nodup := by
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, B'.keys_nodup.sublist (List.filter_sublist.map Prod.fst)⟩
    simp only [List.mem_map, List.mem_filter]
    rintro ⟨p, ⟨_, hp⟩, hpe⟩
    simp [hpe] at hp
  bounded := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · have h := B'.quote_mem_Icc ψ
      refine ⟨?_, ?_⟩ <;> dsimp only <;>
        nlinarith [mul_nonneg (sub_nonneg.mpr hc1) h.1,
          mul_nonneg (sub_nonneg.mpr hc1) (sub_nonneg.mpr h.2)]
    · exact B'.bounded p (List.mem_filter.mp hp).1

lemma floorState_quote (ψ : Sentence) (c : ℚ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (B' : RationalBeliefState) (φ : Sentence) :
    (floorState ψ c hc0 hc1 B').quote φ =
      (if φ = ψ then c else 0) + (1 - (if φ = ψ then c else 0)) * B'.quote φ := by
  change quoteFromEntries
    ((ψ, c + (1 - c) * B'.quote ψ) :: B'.entries.filter fun p => p.1 ≠ ψ) φ = _
  rw [quoteFromEntries_cons]
  by_cases h : φ = ψ
  · subst h; simp
  · rw [if_neg h, if_neg h, quoteFromEntries_filter_ne _ _ _ h]
    simp [RationalBeliefState.quote]

/-! ## Floor schedules and their markets -/

/-- **A floor schedule**: on day `n`, the floor `c n ≤ price (φ n)`, at a level in
`[0, 1]`. -/
structure FloorSchedule where
  /-- The floored sentence of each day. -/
  φ : ℕ → Sentence
  /-- The level of each day. -/
  c : ℕ → ℚ
  c_nonneg : ∀ n, 0 ≤ c n
  c_le_one : ∀ n, c n ≤ 1

namespace FloorSchedule

variable (F : FloorSchedule) (L : Assessment)

/-- The day's lower bounds: the level at the floored sentence, zero elsewhere. -/
def lo (n : ℕ) : Sentence → ℚ := fun ψ => if ψ = F.φ n then F.c n else 0

lemma lo_range (n : ℕ) (ψ : Sentence) : 0 ≤ F.lo n ψ ∧ F.lo n ψ ≤ 1 := by
  unfold lo
  split_ifs
  · exact ⟨F.c_nonneg n, F.c_le_one n⟩
  · exact ⟨le_rfl, zero_le_one⟩

/-- The condition the schedule demands. -/
def condition : Condition := floors F.φ F.c

/-- One day of the construction: price the lifted firm strategy with the pinned market
maker, then lift the prices. -/
noncomputable def step (n : ℕ) (past : List RationalBeliefState) : RationalBeliefState :=
  floorState (F.φ n) (F.c n) (F.c_nonneg n) (F.c_le_one n)
    (MarketMaker (liftStrategy n (F.lo n) ((TradingFirm L).action n past)) past
      (marketMakerError n) (marketMakerError_pos n))

/-- The recursive rational states. -/
noncomputable def states : ℕ → RationalBeliefState
  | n => F.step L n (List.ofFn fun i : Fin n => states i)
termination_by n => n
decreasing_by exact i.isLt

/-- The states before day `n`. -/
noncomputable def past (n : ℕ) : List RationalBeliefState :=
  List.ofFn fun i : Fin n => F.states L i

/-- The market maker's state for the lifted strategy on day `n`. -/
noncomputable def pre (n : ℕ) : RationalBeliefState :=
  MarketMaker (liftStrategy n (F.lo n) ((TradingFirm L).action n (F.past L n))) (F.past L n)
    (marketMakerError n) (marketMakerError_pos n)

lemma states_eq (n : ℕ) :
    F.states L n = floorState (F.φ n) (F.c n) (F.c_nonneg n) (F.c_le_one n) (F.pre L n) := by
  rw [states]
  rfl

/-- The exact rational quote table. -/
noncomputable def quote : ℕ → Sentence → ℚ := fun n => (F.states L n).quote

/-- The price history. -/
noncomputable def history : History := fun n => (F.states L n).toValuation

lemma history_range (day : ℕ) (ψ : Sentence) :
    0 ≤ F.history L day ψ ∧ F.history L day ψ ≤ 1 :=
  (F.states L day).toValuation_mem_Icc ψ

lemma quote_eq (n : ℕ) (ψ : Sentence) :
    F.quote L n ψ = F.lo n ψ + (1 - F.lo n ψ) * (F.pre L n).quote ψ := by
  unfold quote
  rw [states_eq, floorState_quote]
  rfl

lemma rationalHistory_past {n day : ℕ} (hday : day < n) (ψ : Sentence) :
    rationalHistory (F.past L n) day ψ = F.quote L day ψ := by
  simp [rationalHistory, quote, past, hday]

/-- The realized firm's day strategy is the adaptive firm's action on the realized
past. -/
lemma firm_strat (n : ℕ) :
    (tradingFirmTrader L (F.quote L)).strat n = (TradingFirm L).action n (F.past L n) := by
  change TradingFirmAt L (F.quote L) n = TradingFirmAt L (rationalHistory (F.past L n)) n
  apply Workspace.Normativity.Contrib.AssessmentFirm.TradingFirmAt_eq_of_eq_prefix
  intro day hday ψ
  exact (F.rationalHistory_past L hday ψ).symm

/-- Through day `n`, the history is the lifted candidate history. -/
lemma history_eq_lift (n day : ℕ) (hday : day ≤ n) (ψ : Sentence) :
    F.history L day ψ =
      liftHist n (F.lo n)
        (Function.update (beliefHistory (F.past L n)) n (F.pre L n).toValuation) day ψ := by
  rcases hday.eq_or_lt with rfl | hlt
  · rw [liftHist_self, Function.update_self]
    change ((F.quote L day ψ : ℚ) : ℝ) = _
    rw [quote_eq]
    simp [RationalBeliefState.toValuation]
  · rw [liftHist_of_ne _ _ _ hlt.ne, Function.update_of_ne hlt.ne]
    change ((F.quote L day ψ : ℚ) : ℝ) = ((rationalHistory (F.past L n) day ψ : ℚ) : ℝ)
    rw [F.rationalHistory_past L hlt]

/-- The multiplier: the size of the firm's negative position on the floored sentence. -/
noncomputable def mu (n : ℕ) (_ : ℕ) : ℝ :=
  max 0 (-(((tradingFirmTrader L (F.quote L)).strat n).shares (F.history L) (F.φ n)))

/-- **The day inequality of the floor market.** -/
theorem day_le (n : ℕ) (w : Sentence → ℝ) (hw : ∀ ψ, 0 ≤ w ψ ∧ w ψ ≤ 1) :
    ((tradingFirmTrader L (F.quote L)).strat n).value (F.history L) w +
      F.condition.stake (F.mu L) n w ≤ (marketMakerError n : ℝ) := by
  classical
  unfold condition mu
  rw [floors_stake, F.firm_strat L n]
  set T := (TradingFirm L).action n (F.past L n) with hT
  have h := floor_day_le T (beliefHistory (F.past L n)) (F.lo n) (F.lo_range n)
    (F.pre L n).toValuation (F.pre L n).toValuation_mem_Icc (marketMakerError n)
    (fun b => MarketMaker_worldValue_le _ _ _ _ b) w hw
  rw [← T.value_eq_of_eqUpTo (F.history L) _ w (F.history_eq_lift L n)] at h
  have hsh : ∀ ψ, T.shares (liftHist n (F.lo n)
      (Function.update (beliefHistory (F.past L n)) n (F.pre L n).toValuation)) ψ =
      T.shares (F.history L) ψ := fun ψ =>
    (shares_eq_of_eqUpTo T (F.history L) _ (F.history_eq_lift L n) ψ).symm
  simp only [hsh] at h
  suffices hkey : max 0 (-(T.shares (F.history L) (F.φ n))) * (w (F.φ n) - ((F.c n : ℚ) : ℝ)) ≤
      ∑ ψ ∈ T.support, max 0 (-(T.shares (F.history L) ψ)) * (w ψ - ((F.lo n ψ : ℚ) : ℝ)) by
    linarith
  have hother : ∀ ψ ∈ T.support, ψ ≠ F.φ n →
      0 ≤ max 0 (-(T.shares (F.history L) ψ)) * (w ψ - ((F.lo n ψ : ℚ) : ℝ)) := by
    intro ψ _ hne
    have : F.lo n ψ = 0 := by simp [lo, hne]
    rw [this]
    exact mul_nonneg (le_max_left _ _) (by simpa using (hw ψ).1)
  have hlo : F.lo n (F.φ n) = F.c n := by simp [lo]
  by_cases hmem : F.φ n ∈ T.support
  · rw [← Finset.add_sum_erase _ _ hmem, hlo]
    have : 0 ≤ ∑ ψ ∈ T.support.erase (F.φ n),
        max 0 (-(T.shares (F.history L) ψ)) * (w ψ - ((F.lo n ψ : ℚ) : ℝ)) :=
      Finset.sum_nonneg fun ψ hψ =>
        hother ψ (Finset.mem_of_mem_erase hψ) (Finset.ne_of_mem_erase hψ)
    linarith
  · rw [shares_eq_zero_of_not_mem T _ hmem]
    simp only [neg_zero, max_self, zero_mul]
    exact Finset.sum_nonneg fun ψ hψ => hother ψ hψ (fun h => hmem (h ▸ hψ))

/-- The posted price of the floored sentence is at least the level, exactly. -/
theorem floor_holds (n : ℕ) : F.condition.Holds n (F.history L n) := by
  unfold condition
  rw [floors_holds]
  change ((F.c n : ℚ) : ℝ) ≤ ((F.quote L n (F.φ n) : ℚ) : ℝ)
  rw [quote_eq]
  have hlo : F.lo n (F.φ n) = F.c n := by simp [lo]
  rw [hlo]
  have h := mul_nonneg (sub_nonneg.mpr (F.c_le_one n)) ((F.pre L n).quote_mem_Icc (F.φ n)).1
  exact_mod_cast (by linarith : F.c n ≤ F.c n + (1 - F.c n) * (F.pre L n).quote (F.φ n))

/-- **The dual-certified market of a floor schedule.**  Existence of an exactly compliant
market with its certificate, for every assessment and every floor schedule. -/
noncomputable def market : DualCertifiedMarket where
  L := L
  P := F.history L
  quote := F.quote L
  P_eq _ _ := rfl
  P_range := F.history_range L
  C := F.condition
  mu := F.mu L
  mu_nonneg _ _ _ := le_max_left _ _
  mem := F.floor_holds L
  eps n := (marketMakerError n : ℝ)
  eps_pos n := by exact_mod_cast marketMakerError_pos n
  epsTotal := 1
  eps_sum_le N := (sum_marketMakerError_lt_one N).le
  day_le := F.day_le L

@[simp] lemma market_L : (F.market L).L = L := rfl
@[simp] lemma market_C : (F.market L).C = floors F.φ F.c := rfl
lemma market_U : (F.market L).U = 3 := by norm_num [DualCertifiedMarket.U, market]

/-- **Existence** (Tier B, for floor schedules). -/
theorem exists_market :
    ∃ M : DualCertifiedMarket, M.L = L ∧ M.C = floors F.φ F.c ∧ M.U = 3 :=
  ⟨F.market L, rfl, rfl, F.market_U L⟩

end FloorSchedule

/-! ## A8 — the unconstrained market -/

/-- The condition demanding nothing. -/
def emptyCondition : Condition := ⟨fun _ => 0, fun _ _ => ⟨[], 0⟩⟩

open Classical in
/-- The pinned market maker's day bound at every Boolean table on the day's support. -/
lemma marketMaker_day_bitTable_le (Tr : Trader) (n : ℕ) (b : ↥(Tr.strat n).support → Bool) :
    (Tr.strat n).value (marketMakerHistory Tr) (supportBitWorld (Tr.strat n) b) ≤
      (marketMakerError n : ℝ) := by
  have hmm := MarketMaker_worldValue_le (Tr.strat n)
    (marketMakerPast (marketMakerStates Tr) n) (marketMakerError n) (marketMakerError_pos n) b
  have hstate : MarketMaker (Tr.strat n) (marketMakerPast (marketMakerStates Tr) n)
      (marketMakerError n) (marketMakerError_pos n) = marketMakerStates Tr n := by
    rw [marketMakerStates]
    rfl
  rw [hstate] at hmm
  rwa [(Tr.strat n).value_eq_of_eqUpTo _ (marketMakerHistory Tr) _
    (fun day hday φ => congrFun (candidate_marketMakerHistory_eq_upTo Tr n day hday) φ)] at hmm

/-- **The unconstrained market is dual-certified** (A8): the recursive market of
`AssessmentFirm`, the empty condition, every multiplier zero. -/
noncomputable def plainMarket (L : Assessment) : DualCertifiedMarket where
  L := L
  P := AssessmentFirm.history L
  quote := AssessmentFirm.quote L
  P_eq := history_eq_quote_cast L
  P_range := AssessmentFirm.history_range L
  C := emptyCondition
  mu _ _ := 0
  mu_nonneg _ _ _ := le_rfl
  mem _ j hj := absurd hj (Nat.not_lt_zero j)
  eps n := (marketMakerError n : ℝ)
  eps_pos n := by exact_mod_cast marketMakerError_pos n
  epsTotal := 1
  eps_sum_le N := (sum_marketMakerError_lt_one N).le
  day_le n w hw := by
    have hstake : emptyCondition.stake (fun _ _ => (0 : ℝ)) n w = 0 := by
      simp [Condition.stake, emptyCondition]
    rw [hstake, add_zero, tradingFirmTrader_quote_eq_firmTrader, history_eq_marketMakerHistory]
    exact value_le_of_bitTables _ _ _ (marketMaker_day_bitTable_le (firmTrader L) n) w hw

/-! ## Inhabitants -/

/-- **A2 and A3, inhabited trivially**: the unconstrained market's condition is entailed
and its account is bounded. -/
theorem plainMarket_entailed (L : Assessment) :
    (plainMarket L).C.Entailed (plainMarket L).L ∧ (plainMarket L).AccountBounded 0 := by
  have h : (plainMarket L).C.Entailed (plainMarket L).L :=
    fun n v _ j hj => absurd hj (Nat.not_lt_zero j)
  exact ⟨h, (plainMarket L).accountBounded_of_entailed h⟩

/-- The process asserting atom `0` from the start. -/
def assertProcess : DeductiveProcess where
  D _ := {atomP}
  mono _ := Finset.Subset.refl _

/-- The schedule pinning atom `0` at price one every day. -/
def pinSchedule : FloorSchedule := ⟨fun _ => atomP, fun _ => 1, fun _ => zero_le_one, fun _ => le_rfl⟩

/-- The deductive region of the stage `{p}` on the fragment `[p]` is the point `p = 1`. -/
lemma deductiveRegion_assert (x : Sentence → ℝ) :
    deductiveRegion {atomP} [atomP] x ↔ x atomP = 1 := by
  have hvert : deductiveVertices {atomP} [atomP] = {fun _ => (1 : ℝ)} := by
    ext y
    simp only [deductiveVertices, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨v, hv, rfl⟩ := admissiblePatterns_sound {atomP} [atomP] hw
      funext i
      rw [vertex_map]
      have hi : ([atomP] : List Sentence)[i] = atomP := by
        have := i.isLt
        simp only [List.length_singleton, Nat.lt_one_iff] at this
        simp
      have hholds : v.Holds atomP := hv atomP (Finset.mem_singleton_self _)
      rw [hi]
      simp [ratPayout, hholds]
    · rintro rfl
      refine ⟨[atomP].map (ratPayout witnessWorld),
        admissiblePatterns_complete {atomP} [atomP] witnessWorld witnessWorld_consistent, ?_⟩
      funext i
      rw [vertex_map]
      have hi : ([atomP] : List Sentence)[i] = atomP := by
        have := i.isLt
        simp only [List.length_singleton, Nat.lt_one_iff] at this
        simp
      have hholds : witnessWorld.Holds atomP :=
        witnessWorld_consistent atomP (Finset.mem_singleton_self _)
      rw [hi]
      simp [ratPayout, hholds]
  unfold deductiveRegion
  rw [hvert, convexHull_singleton, Set.mem_singleton_iff]
  constructor
  · intro h
    have := congrFun h ⟨0, by simp⟩
    simpa [restrictTo] using this
  · intro h
    funext i
    have hi : ([atomP] : List Sentence)[i] = atomP := by
      have := i.isLt
      simp only [List.length_singleton, Nat.lt_one_iff] at this
      simp
    simp only [restrictTo, hi, h]

/-- **A3's deductive instance, inhabited**: a nontrivial region, exact membership, and
the conclusion — prices on the fragment in the hull, here the point `p = 1`. -/
theorem deductive_witness :
    (∀ Tr : Trader, EfficientlyComputable Tr →
        ¬ Tr.Exploits (pinSchedule.market (ofDeductiveProcess assertProcess)).P
          assertProcess) ∧
      ∀ n, (pinSchedule.market (ofDeductiveProcess assertProcess)).P n atomP = 1 := by
  have h := (pinSchedule.market (ofDeductiveProcess assertProcess)).deductive_exact
    assertProcess (fun _ _ => Iff.rfl) (fun _ => [atomP]) (fun n x hx => by
      rw [FloorSchedule.market_C, floors_holds]
      change ((1 : ℚ) : ℝ) ≤ x atomP ↔ deductiveRegion {atomP} [atomP] x
      rw [deductiveRegion_assert]
      constructor
      · intro h; exact le_antisymm (hx atomP).2 (by simpa using h)
      · intro h; simp [h])
  exact ⟨h.1, fun n => (deductiveRegion_assert _).mp (h.2 n)⟩

/-! ### A4's witness

One floor `c ≤ price p` on day `0`; `p` is refuted from day `1`.  The reserve `(c, 1 - c)`
on (`p` true, `p` false), then `(0, 1 - c)`, bounds the account where `p` is false by
`-U c / (1 - c)`.  A reserve supported only on worlds live at the last day would have to
put all its mass where `p` is false, and the day-`0` row would average to `-c`. -/

/-- The process refuting atom `0` from day `1`. -/
def refuteProcess : DeductiveProcess where
  D n := if n = 0 then ∅ else {∼atomP}
  mono n := by
    by_cases h : n = 0
    · simp [h]
    · simp [h]

/-- One floor at level `c` on day `0`, nothing after. -/
def oneFloor (c : ℚ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : FloorSchedule where
  φ _ := atomP
  c n := if n = 0 then c else 0
  c_nonneg n := by split_ifs <;> [exact hc0; exact le_rfl]
  c_le_one n := by split_ifs <;> [exact hc1; exact zero_le_one]

lemma allTrue_payout_atomP : allTrue.payout atomP = 1 :=
  payout_of_holds (by exact trivial)

lemma allFalse_payout_atomP : allFalse.payout atomP = 0 :=
  payout_of_not_holds (allFalse_not_holds_atom 0)

/-- The prefix reserve of the example. -/
noncomputable def oneFloorReserve (c : ℚ) (hc0 : 0 < c) (hc1 : c < 1) :
    PrefixReserve (ofDeductiveProcess refuteProcess) (floors (oneFloor c hc0.le hc1.le).φ
      (oneFloor c hc0.le hc1.le).c) 1 where
  Ω := Bool
  world b := if b then allTrue else allFalse
  r n b := if b then (if n = 0 then (c : ℝ) else 0) else 1 - (c : ℝ)
  nonneg n _ b := by
    have h0 : (0 : ℝ) < c := by exact_mod_cast hc0
    have h1 : (c : ℝ) < 1 := by exact_mod_cast hc1
    cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;> [linarith; split_ifs <;> linarith]
  anti n _ b := by
    have h0 : (0 : ℝ) < c := by exact_mod_cast hc0
    cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
      [exact le_rfl; (split_ifs <;> first | linarith | simp_all)]
  mass := by
    rw [Fintype.sum_bool]
    simp
  live n hn b hpos := by
    cases b
    · simp only [Bool.false_eq_true, if_false]
      intro φ hφ
      by_cases h : n = 0
      · simp [refuteProcess, h] at hφ
      · simp only [refuteProcess, h, if_false, Finset.mem_singleton] at hφ
        subst hφ
        rw [PCWorld.holds_neg]
        exact allFalse_not_holds_atom 0
    · simp only [if_true] at hpos ⊢
      by_cases h : n = 0
      · subst h
        intro φ hφ
        simp [refuteProcess] at hφ
      · simp [h] at hpos
  row n hn j hj := by
    rw [Fintype.sum_bool]
    simp only [floors, Bet.floor_eval, oneFloor, if_true, Bool.false_eq_true, if_false,
      allTrue_payout_atomP, allFalse_payout_atomP]
    by_cases h : n = 0
    · simp only [h, if_true]
      apply le_of_eq
      ring
    · simp [h]

/-- **A4, inhabited.**  In the one-floor market, the account through day `1` at the world
refuting `p` — the only kind live at day `1` — is at least `-3 c / (1 - c)`. -/
theorem oneFloor_reserve_bound (c : ℚ) (hc0 : 0 < c) (hc1 : c < 1) :
    (ofDeductiveProcess refuteProcess).Live 1 allFalse ∧
      -(3 * (c : ℝ) / (1 - (c : ℝ))) ≤
        ((oneFloor c hc0.le hc1.le).market (ofDeductiveProcess refuteProcess)).C.account
          ((oneFloor c hc0.le hc1.le).market (ofDeductiveProcess refuteProcess)).mu 1
          allFalse.payout := by
  have h1 : (c : ℝ) < 1 := by exact_mod_cast hc1
  constructor
  · intro φ hφ
    simp only [refuteProcess, Nat.one_ne_zero, if_false, Finset.mem_singleton] at hφ
    subst hφ
    rw [PCWorld.holds_neg]
    exact allFalse_not_holds_atom 0
  · have h := ((oneFloor c hc0.le hc1.le).market
      (ofDeductiveProcess refuteProcess)).reserve_bound (oneFloorReserve c hc0 hc1) false
      (by change (0 : ℝ) < 1 - (c : ℝ); linarith)
    rw [FloorSchedule.market_U] at h
    have hr : (oneFloorReserve c hc0 hc1).r 1 false = 1 - (c : ℝ) := rfl
    have hw : (oneFloorReserve c hc0 hc1).world false = allFalse := rfl
    rw [hr, hw] at h
    have he : (3 : ℝ) * (1 - (1 - (c : ℝ))) / (1 - (c : ℝ)) = 3 * (c : ℝ) / (1 - (c : ℝ)) := by
      ring
    rw [he] at h
    exact h

/-! ### A7's witness

A fresh atom each day at a constant level `c < 1`, each settled true the next day.  The
realized truth values are all one, so the frequency hypothesis holds with `γ = 1 - c`, and
the bridge bounds the account — in contrast with the levels `1 - 2^-(n+1)` of
`freshFloor`, which no compliant history survives. -/

/-- A fresh atom each day at the constant level `c`. -/
def constantFresh (c : ℚ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : FloorSchedule :=
  ⟨fun n => .atom n, fun _ => c, fun _ => hc0, fun _ => hc1⟩

/-- **A7, inhabited.**  The constant-level fresh-floor market over the revealing process:
the floors are not entailed, the prices satisfy them exactly, the account is bounded
below, and no efficiently computable trader exploits it. -/
theorem constantFresh_unexploited (c : ℚ) (hc0 : 0 < c) (hc1 : c < 1) :
    (∀ n, ∃ v, (ofDeductiveProcess revealProcess).Live n v ∧
        ¬ (floors (fun n => .atom n) (fun _ => c)).Holds n v.payout) ∧
      (∀ n, (c : ℝ) ≤
        ((constantFresh c hc0.le hc1.le).market (ofDeductiveProcess revealProcess)).P n
          (.atom n)) ∧
      (∃ B, ((constantFresh c hc0.le hc1.le).market
        (ofDeductiveProcess revealProcess)).AccountBounded B) ∧
      ∀ Tr : Trader, EfficientlyComputable Tr →
        ¬ (ofDeductiveProcess revealProcess).Exploits Tr
          ((constantFresh c hc0.le hc1.le).market (ofDeductiveProcess revealProcess)).P := by
  set M := (constantFresh c hc0.le hc1.le).market (ofDeductiveProcess revealProcess) with hM
  have hc0' : (0 : ℝ) < c := by exact_mod_cast hc0
  have hbound : M.AccountBounded ((c : ℝ) * ∑' n, M.mu n 0) := by
    refine M.accountBounded_of_frequency (fun n => .atom n) c hc0 hc1 rfl (fun _ => true)
      (fun N v hv i hi => ?_) (fun n => ?_) (1 - (c : ℝ)) (by
        have : (c : ℝ) < 1 := by exact_mod_cast hc1
        linarith) (fun _ => ⟨0, fun N _ => ?_⟩)
    · refine ⟨fun _ => rfl, fun _ => hv _ ?_⟩
      simp only [revealProcess, Finset.mem_image, Finset.mem_range]
      exact ⟨i, hi, rfl⟩
    · refine ⟨prefixWorld (n + 1), ?_, (prefixWorld_holds_atom (n + 1) n).mpr (Nat.lt_succ_self n)⟩
      intro φ hφ
      simp only [revealProcess, Finset.mem_image, Finset.mem_range] at hφ
      obtain ⟨k, hk, rfl⟩ := hφ
      exact (prefixWorld_holds_atom (n + 1) k).mpr (Nat.lt_succ_of_lt hk)
    · apply le_of_eq
      rw [show (c : ℝ) + (1 - (c : ℝ)) = 1 by ring, one_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [DualCertifiedMarket.realized]
  refine ⟨fun n => ⟨prefixWorld n, prefixWorld_live n, ?_⟩, fun n => ?_, ⟨_, hbound⟩,
    fun Tr hTr => M.no_efficient_trader_exploits hbound Tr hTr⟩
  · rw [floors_holds, payout_of_not_holds
      (fun h => lt_irrefl n ((prefixWorld_holds_atom n n).mp h))]
    linarith
  · have h := M.mem n
    rw [hM, FloorSchedule.market_C, floors_holds] at h
    exact h

end Workspace.Normativity.Contrib.ExactConditions

#print axioms Workspace.Normativity.Contrib.ExactConditions.liftDay_rank
#print axioms Workspace.Normativity.Contrib.ExactConditions.liftDay_denoteWith
#print axioms Workspace.Normativity.Contrib.ExactConditions.liftStrategy_shares
#print axioms Workspace.Normativity.Contrib.ExactConditions.floor_term_le
#print axioms Workspace.Normativity.Contrib.ExactConditions.floor_day_le
#print axioms Workspace.Normativity.Contrib.ExactConditions.value_le_of_bitTables
#print axioms Workspace.Normativity.Contrib.ExactConditions.floorState_quote
#print axioms Workspace.Normativity.Contrib.ExactConditions.FloorSchedule.history_eq_lift
#print axioms Workspace.Normativity.Contrib.ExactConditions.FloorSchedule.day_le
#print axioms Workspace.Normativity.Contrib.ExactConditions.FloorSchedule.floor_holds
#print axioms Workspace.Normativity.Contrib.ExactConditions.FloorSchedule.market
#print axioms Workspace.Normativity.Contrib.ExactConditions.FloorSchedule.exists_market
#print axioms Workspace.Normativity.Contrib.ExactConditions.plainMarket
#print axioms Workspace.Normativity.Contrib.ExactConditions.plainMarket_entailed
#print axioms Workspace.Normativity.Contrib.ExactConditions.deductiveRegion_assert
#print axioms Workspace.Normativity.Contrib.ExactConditions.deductive_witness
#print axioms Workspace.Normativity.Contrib.ExactConditions.oneFloorReserve
#print axioms Workspace.Normativity.Contrib.ExactConditions.oneFloor_reserve_bound
#print axioms Workspace.Normativity.Contrib.ExactConditions.constantFresh_unexploited
