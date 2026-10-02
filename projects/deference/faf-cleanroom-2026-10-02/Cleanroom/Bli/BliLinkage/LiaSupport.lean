import LogicalInduction.Construction.LIA
import LogicalInduction.Framework.Emission.RpnSentence

/-!
# `bli-linkage` — FAF's LIA lists at most polynomially many sentences per day
(repair round 3, audit r3 adversarial B1 / fidelity N1)

Pure FAF plumbing, no package definitions: a bound on the **support** (the finite set of
listed keys) of FAF's day-`n` LIA belief state `liaStates DP n`, for every deductive process
`DP`. The chain, each link read off FAF's definitions:

1. `liaStates DP n` is the `MarketMaker`'s accepted candidate against the day-`n` trading
   firm, and acceptance (`MarketMakerAccepts`, first conjunct) puts the candidate's support
   inside the firm's strategy support (`liaStates_support_subset_firm`).
2. The firm's day-`n` strategy `TradingFirmAt` is `Strategy.join` over `j ≤ n` of components,
   each a `join` of budgeted (`BudgeterAt`: empty or `scaleBy`) and constant-scaled copies of
   the gated enumerated trader `firmRawTrader j = (enumeratedTrader j).gate j`. `scaleBy`,
   `scaleConst` and `gate` do not enlarge the support and `join` unions it, so the firm's
   support lies in `⋃_{j ≤ n} ((enumeratedTrader j).strat n).support`
   (`tradingFirmAt_support_subset`).
3. `(enumeratedTrader j).strat n = strategyOfTokens n (unRpn (undigitize (machineTokens j n)))`,
   and each stage of the decoder is length-non-increasing up to one token: `undigitize` emits
   one token per closing digit (`undigitize_length_le`), `unRpn` contracts sentence blocks
   (`unRpn_length_le`, via FAF's `parseRpn_length_lt`), and the streaming trade parser appends
   at most one trade per token (`streamStep_some_length_le`, `deserializeTrades_length_le`).
   With FAF's clock bound `length_machineTokens_le` (`(machineTokens j n).length ≤ progClock j n`)
   this gives `((enumeratedTrader j).strat n).trades.length ≤ progClock j n + 1`.
4. Hence **`liaStates_support_card_le`**: `(liaStates DP n).support.card ≤ ∑_{j ≤ n} (progClock j n + 1)`,
   and with `progCoeff j, progDeg j ≤ j` (Mathlib's `Nat.unpair_left_le`/`_right_le`)
   **`liaStates_support_card_le_poly`**: `≤ ∑_{j ≤ n} (j (n+1)^j + j + 1)`; on day `4` that
   is `2945` (`liaStates_support_card_le_day4`).

Used by `LiaPackage` to refute the round-2 OPEN `lia_small_coherent_mixture_exists`: the K3
package at the LIA forces `2^(2^n − 2)` small tautologies to be listed on day `n` — `16384`
on day `4` against the `2945` available.
-/

namespace Cleanroom.Bli.BliLinkage

open LogicalInduction LogicalInduction.MachineExec Finset

/-! ## 1. The streaming trade parser emits at most one trade per token -/

/-- The number of trades held by a parser state (`0` for the rejected state).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def streamTradeCount : Option EF.StreamState → ℕ
  | none => 0
  | some s => s.2.2.length

/-- One token of FAF's streaming strategy decoder appends at most one trade (only mode `4`
appends, and exactly one).
Source: none: infrastructure (FAF `EF.streamStep`)
Kind: L
Fidelity: n/a -/
lemma streamStep_some_length_le (st : EF.StreamState) (t : ℕ) (s' : EF.StreamState)
    (h : EF.streamStep (some st) t = some s') : s'.2.2.length ≤ st.2.2.length + 1 := by
  obtain ⟨⟨mode, pending⟩, efst, trades⟩ := st
  simp only [EF.streamStep] at h
  split_ifs at h <;>
    first
      | (cases h <;> simp)
      | (split at h <;> (cases h <;> simp))
      | (rw [Option.map_eq_some_iff] at h; obtain ⟨a, -, rfl⟩ := h; simp)

/-- The trade count grows by at most one per token.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma streamStep_tradeCount_le (s : Option EF.StreamState) (t : ℕ) :
    streamTradeCount (EF.streamStep s t) ≤ streamTradeCount s + 1 := by
  rcases s with _ | st
  · simp [EF.streamStep, streamTradeCount]
  · rcases h : EF.streamStep (some st) t with _ | s'
    · simp [streamTradeCount]
    · exact streamStep_some_length_le st t s' h

/-- Running the decoder over a token list adds at most the list's length in trades.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma streamReadFrom_tradeCount_le (toks : List ℕ) : ∀ s : Option EF.StreamState,
    streamTradeCount (EF.streamReadFrom toks s) ≤ streamTradeCount s + toks.length := by
  induction toks with
  | nil => intro s; simp [EF.streamReadFrom]
  | cons t rest ih =>
      intro s
      have h1 := ih (EF.streamStep s t)
      have h2 := streamStep_tradeCount_le s t
      simp only [EF.streamReadFrom, List.foldl_cons, List.length_cons] at h1 ⊢
      omega

/-- A successfully decoded strategy has at most as many trades as the stream has tokens.
Source: none: infrastructure (FAF `deserializeTrades`)
Kind: L
Fidelity: n/a -/
lemma deserializeTrades_length_le {toks : List ℕ} {l : List (EF × Sentence)}
    (h : deserializeTrades toks = some l) : l.length ≤ toks.length := by
  unfold deserializeTrades at h
  split at h
  · rename_i l' heq
    cases h
    have := streamReadFrom_tradeCount_le toks (some EF.streamInitial)
    rw [heq] at this
    simpa [streamTradeCount, EF.streamInitial] using this
  · cases h

/-- `strategyOfTokens` validates the decoded list or returns the empty strategy; either way
at most one trade per token.
Source: none: infrastructure (FAF `strategyOfTokens`)
Kind: L
Fidelity: n/a -/
lemma strategyOfTokens_trades_length_le (n : ℕ) (toks : List ℕ) :
    (strategyOfTokens n toks).trades.length ≤ toks.length := by
  unfold strategyOfTokens
  split
  · simp
  · next trades hdecode =>
      split_ifs
      · exact deserializeTrades_length_le hdecode
      · simp

/-! ## 2. `undigitize` and `unRpn` do not lengthen their input (by more than one) -/

/-- The digit fold emits one token per closing digit, so at most one per digit.
Source: none: infrastructure (FAF `undigitizeStep`)
Kind: L
Fidelity: n/a -/
lemma foldl_undigitizeStep_length_le (ds : List ℕ) : ∀ (out : List ℕ) (acc pow : ℕ),
    (List.foldl undigitizeStep (out, acc, pow) ds).1.length ≤ out.length + ds.length := by
  induction ds with
  | nil => intro out acc pow; simp
  | cons d rest ih =>
      intro out acc pow
      rw [List.foldl_cons]
      simp only [undigitizeStep]
      split_ifs
      · exact (ih out _ _).trans (by simp)
      · refine (ih (out ++ [acc]) 0 1).trans ?_
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega

/-- `undigitize` is length-non-increasing.
Source: none: infrastructure (FAF `undigitize`)
Kind: L
Fidelity: n/a -/
lemma undigitize_length_le (ds : List ℕ) : (undigitize ds).length ≤ ds.length := by
  have := foldl_undigitizeStep_length_le ds [] 0 1
  simpa [undigitize] using this

/-- `unRpnTokens` contracts every sentence block to a pair code and otherwise copies, so
its output is at most one token longer than its input (the slack is the poison code of a
failed block parse at the end of the stream). Uses FAF's `parseRpn_length_lt`.
Source: none: infrastructure (FAF `unRpnTokens`, `parseRpn_length_lt`)
Kind: L
Fidelity: n/a -/
lemma unRpnTokens_length_le : ∀ (fuel : ℕ) (ts : List ℕ),
    (unRpnTokens fuel ts).length ≤ ts.length + 1
  | 0, ts => by cases ts <;> simp [unRpnTokens]
  | _ + 1, [] => by simp [unRpnTokens]
  | fuel + 1, t :: rest => by
      rw [unRpnTokens_cons]
      split_ifs
      · rcases hp : parseRpn rest.length rest with _ | ⟨φ, _ | ⟨d, r2⟩⟩
        · simp
        · simp
        · have hlt := parseRpn_length_lt _ _ _ _ hp
          have ih := unRpnTokens_length_le fuel r2
          simp only [List.length_cons] at hlt ⊢
          omega
      · rcases hp : parseRpn rest.length rest with _ | ⟨φ, r1⟩
        · simp
        · have hlt := parseRpn_length_lt _ _ _ _ hp
          have ih := unRpnTokens_length_le fuel r1
          simp only [List.length_cons]
          omega
      · rcases rest with _ | ⟨c, r⟩
        · simp
        · have ih := unRpnTokens_length_le fuel r
          simp only [List.length_cons]
          omega
      · rcases rest with _ | ⟨c, r⟩
        · simp
        · have ih := unRpnTokens_length_le fuel r
          simp only [List.length_cons]
          omega
      · have ih := unRpnTokens_length_le fuel rest
        simp only [List.length_cons]
        omega

/-- `unRpn` is length-non-increasing up to one token.
Source: none: infrastructure (FAF `unRpn`)
Kind: L
Fidelity: n/a -/
lemma unRpn_length_le (ts : List ℕ) : (unRpn ts).length ≤ ts.length + 1 :=
  unRpnTokens_length_le _ _

/-! ## 3. The enumerated trader's day-`n` trade count is bounded by its clock -/

/-- **FAF's `j`-th enumerated trader places at most `progClock j n + 1` trades on day `n`**:
its token stream is clocked (`length_machineTokens_le`) and the decoder emits at most one
trade per token.
Source: none: infrastructure (FAF `enumeratedTrader`, `length_machineTokens_le`)
Kind: P
Fidelity: n/a -/
theorem enumeratedTrader_trades_length_le (j n : ℕ) :
    ((enumeratedTrader j).strat n).trades.length ≤ progClock j n + 1 := by
  rw [enumeratedTrader_strat]
  exact (strategyOfTokens_trades_length_le _ _).trans
    ((unRpn_length_le _).trans
      (Nat.add_le_add_right ((undigitize_length_le _).trans (length_machineTokens_le j n)) 1))

/-! ## 4. Supports through `scaleBy`, `scaleConst`, `gate`, `join`, `BudgeterAt` -/

/-- A strategy's support has at most as many sentences as it has trades.
Source: none: infrastructure (FAF `Strategy.support`)
Kind: L
Fidelity: n/a -/
lemma support_card_le_length {n : ℕ} (T : Strategy n) : T.support.card ≤ T.trades.length :=
  Finset.card_image_le.trans (List.toFinset_card_le _)

/-- Scaling by a feature keeps the support.
Source: none: infrastructure (FAF `Strategy.scaleBy`)
Kind: L
Fidelity: n/a -/
lemma support_scaleBy {n : ℕ} (e : EF) (he : e.rank ≤ n) (T : Strategy n) :
    (T.scaleBy e he).support = T.support := by
  ext φ
  simp [Strategy.support, Strategy.scaleBy]

/-- Scaling by a constant keeps the support.
Source: none: infrastructure (FAF `scaleConst`)
Kind: L
Fidelity: n/a -/
lemma support_scaleConst {n : ℕ} (q : ℚ) (T : Strategy n) :
    (T.scaleConst q).support = T.support :=
  support_scaleBy _ _ _

/-- A sentence in the support of a `join` is in the support of a member.
Source: none: infrastructure (FAF `Strategy.join`)
Kind: L
Fidelity: n/a -/
lemma exists_of_mem_support_join {n : ℕ} {ts : List (Strategy n)} {φ : Sentence}
    (h : φ ∈ (Strategy.join ts).support) : ∃ T ∈ ts, φ ∈ T.support := by
  simp only [Strategy.support, Strategy.join, Finset.mem_image, List.mem_toFinset,
    List.mem_flatMap] at h ⊢
  obtain ⟨p, ⟨T, hT, hp⟩, rfl⟩ := h
  exact ⟨T, hT, p, hp, rfl⟩

/-- The zero trader's strategies have empty support.
Source: none: infrastructure (FAF `Trader.zero`)
Kind: L
Fidelity: n/a -/
lemma support_zero_strat (n : ℕ) : (Trader.zero.strat n).support = ∅ := by
  simp [Trader.zero, Strategy.support]

/-- The budgeter's day action is empty or a `scaleBy` of the raw day action.
Source: none: infrastructure (FAF `BudgeterAt`)
Kind: L
Fidelity: n/a -/
lemma budgeterAt_support_subset (DP : DeductiveProcess) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) :
    (BudgeterAt DP Tr b Q n).support ⊆ (Tr.strat n).support := by
  unfold BudgeterAt
  split_ifs
  · simp [Strategy.support]
  · rw [support_scaleBy]

/-- The gated enumerated trader's support is inside the enumerated trader's.
Source: none: infrastructure (FAF `firmRawTrader`, `Trader.gate`)
Kind: L
Fidelity: n/a -/
lemma firmRawTrader_support_subset (j n : ℕ) :
    ((firmRawTrader j).strat n).support ⊆ ((enumeratedTrader j).strat n).support := by
  show (if j ≤ n then (enumeratedTrader j).strat n else Trader.zero.strat n).support ⊆ _
  split_ifs
  · exact Finset.Subset.refl _
  · rw [support_zero_strat]; exact Finset.empty_subset _

/-- One firm component's support is inside its enumerated trader's day-`n` support.
Source: none: infrastructure (FAF `tradingFirmComponentAt`)
Kind: L
Fidelity: n/a -/
lemma tradingFirmComponentAt_support_subset (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ)
    (n j : ℕ) :
    (tradingFirmComponentAt DP Q n j).support ⊆ ((enumeratedTrader j).strat n).support := by
  intro φ hφ
  unfold tradingFirmComponentAt at hφ
  obtain ⟨T, hT, hφT⟩ := exists_of_mem_support_join hφ
  simp only [tradingFirmBudgetComponents, List.mem_append, List.mem_map, List.mem_range,
    List.mem_singleton] at hT
  rcases hT with ⟨r, -, rfl⟩ | rfl
  · rw [support_scaleConst] at hφT
    exact firmRawTrader_support_subset j n (budgeterAt_support_subset _ _ _ _ _ hφT)
  · rw [support_scaleConst] at hφT
    exact firmRawTrader_support_subset j n hφT

/-- **The day-`n` trading firm's support lies in the union of the enumerated traders'
day-`n` supports over `j ≤ n`.**
Source: none: infrastructure (FAF `TradingFirmAt`)
Kind: P
Fidelity: n/a -/
theorem tradingFirmAt_support_subset (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ) (n : ℕ) :
    (TradingFirmAt DP Q n).support ⊆
      (Finset.range (n + 1)).biUnion fun j => ((enumeratedTrader j).strat n).support := by
  intro φ hφ
  unfold TradingFirmAt at hφ
  obtain ⟨T, hT, hφT⟩ := exists_of_mem_support_join hφ
  simp only [List.mem_map, List.mem_range] at hT
  obtain ⟨j, hj, rfl⟩ := hT
  exact Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hj,
    tradingFirmComponentAt_support_subset DP Q n j hφT⟩

/-- **The day-`n` trading firm trades at most `∑_{j ≤ n} (progClock j n + 1)` distinct
sentences**, whatever the deductive process and the price history.
Source: none: infrastructure (FAF `TradingFirmAt`, `length_machineTokens_le`)
Kind: P
Fidelity: n/a -/
theorem tradingFirmAt_support_card_le (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ) (n : ℕ) :
    (TradingFirmAt DP Q n).support.card ≤ ∑ j ∈ Finset.range (n + 1), (progClock j n + 1) :=
  (Finset.card_le_card (tradingFirmAt_support_subset DP Q n)).trans
    (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j _ =>
      (support_card_le_length _).trans (enumeratedTrader_trades_length_le j n)))

/-! ## 5. The LIA's day-`n` support -/

/-- FAF's market maker accepts only candidates whose support lies inside the strategy's
support (`MarketMakerAccepts`, first conjunct), so the LIA's day-`n` listed keys are among
the sentences the day-`n` trading firm trades.
Source: none: infrastructure (FAF `liaStates`, `MarketMaker_accepts`; audit r3 adversarial probe `SmallTautologiesListed.liaStates_support_subset_firm`, adopted)
Kind: L
Fidelity: n/a -/
theorem liaStates_support_subset_firm (DP : DeductiveProcess) (n : ℕ) :
    (liaStates DP n).support ⊆
      ((TradingFirm DP).action n (List.ofFn fun i : Fin n => liaStates DP i)).support := by
  rw [liaStates]
  exact (MarketMaker_accepts _ _ _ _).1

/-- **FAF's LIA lists at most `∑_{j ≤ n} (progClock j n + 1)` sentences on day `n`**, for
every deductive process.
Source: none: infrastructure (this run, repair r3; closes the "one open step" of audit r3 adversarial B1)
Kind: P
Fidelity: n/a -/
theorem liaStates_support_card_le (DP : DeductiveProcess) (n : ℕ) :
    (liaStates DP n).support.card ≤ ∑ j ∈ Finset.range (n + 1), (progClock j n + 1) :=
  (Finset.card_le_card (liaStates_support_subset_firm DP n)).trans
    (tradingFirmAt_support_card_le DP _ n)

/-- The index-`j` clock is at most `j (n+1)^j + j` (`progCoeff j, progDeg j ≤ j` by the
pairing bounds).
Source: none: infrastructure (FAF `progClock`; Mathlib `Nat.unpair_left_le`/`_right_le`)
Kind: L
Fidelity: n/a -/
lemma progClock_le (j n : ℕ) : progClock j n ≤ j * (n + 1) ^ j + j := by
  have h1 : progCoeff j ≤ j := by
    unfold progCoeff
    exact (Nat.unpair_right_le _).trans (Nat.unpair_left_le _)
  have h2 : progDeg j ≤ j := Nat.unpair_right_le _
  unfold progClock
  exact Nat.add_le_add (Nat.mul_le_mul h1 (Nat.pow_le_pow_right (Nat.succ_pos n) h2)) h1

/-- **FAF's LIA lists at most `∑_{j ≤ n} (j (n+1)^j + j + 1)` sentences on day `n`** —
polynomially many in `n` for each `j`, and far below `2^(2^n − 2)` from day `4` on.
Source: none: infrastructure (this run, repair r3)
Kind: P
Fidelity: n/a -/
theorem liaStates_support_card_le_poly (DP : DeductiveProcess) (n : ℕ) :
    (liaStates DP n).support.card ≤ ∑ j ∈ Finset.range (n + 1), (j * (n + 1) ^ j + j + 1) :=
  (liaStates_support_card_le DP n).trans
    (Finset.sum_le_sum fun j _ => Nat.add_le_add_right (progClock_le j n) 1)

/-- On day `4` FAF's LIA lists at most `2945` sentences (the day-`4` value of the polynomial
bound), for every deductive process.
Source: none: infrastructure (this run, repair r3)
Kind: L
Fidelity: n/a -/
theorem liaStates_support_card_le_day4 (DP : DeductiveProcess) :
    (liaStates DP 4).support.card ≤ 2945 :=
  (liaStates_support_card_le_poly DP 4).trans (by norm_num [Finset.sum_range_succ])

end Cleanroom.Bli.BliLinkage
