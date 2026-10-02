import Cleanroom.Bli.BliOverlay.AttemptB.Mentioned
import Cleanroom.Bli.BliFound.Witnesses
import LogicalInduction.Construction.TradingFirm

/-!
# `bli-overlay` (attempt B) · FirmSupport: the firm-support lemma (T2, F2)

`firm_mentioned_small`: from some day `N₀` on, every sentence FAF's trading firm's day-`n`
strategy `TradingFirmAt DP Q n` mentions (traded, or a price leaf of a coefficient) is small
on day `n` (`tokenSize φ ≤ 2^{2^n}`), uniformly in the process `DP` and the table `Q`.

Three steps, all derived:

1. **Structure** (`mentionedBy_TradingFirmAt_iff`): the firm's day-`n` mentioned set is the
   union over the open indices `j ≤ n` of the mentioned sets of the enumerated raw traders
   `(enumeratedTrader j).strat n` — independent of `DP` and `Q`. The budgeter's coefficients
   (`budgetScaleFeature`, a `listMin` of `safeRecip`s of `worldValueFeature`s) carry only
   day-`n` price leaves of the raw strategy's traded sentences; `rawPriorWorthRat` and
   `priorBudgetBreach` read `Q` as data, not as leaves.
2. **Size per index** (`tokenSize_le_of_mentionedBy_enumerated`): the raw day-`n` strategy of
   index `j` is `strategyOfOutput n w` for the machine's output word `w`, so bli-found's
   `tokenSize_le_bridgeBound_of_mentionedBy` bounds every mentioned sentence by
   `bridgeBound C (machineTokens j n).length ≤ 2^((C+6)(progClock j n + 1))`.
3. **Arithmetic** (`firmClock_arith`): `(C+6)(progClock j n + 1) ≤ 2^n` for all `j ≤ n` once
   `n ≥ (C+16)^2`, through the square-root bounds on `Nat.unpair` (both components of
   `unpair m` are `≤ sqrt m`, so the clock's coefficient and degree at index `j ≤ n` are
   `≤ sqrt n`).

The `N₀` this proof yields is `(C + 16)^2` where `C` is the structured-escape constant of
`tokenSize_le_of_structured` (`C = 10` in its proof, so `N₀ = 676`).
-/

namespace Cleanroom.Bli.BliOverlay.AttemptB

open LogicalInduction LogicalInduction.MachineExec LO.Propositional Cleanroom.Bli.BliFound

/-! ## Step 1: structure of the firm's mentioned set -/

/-- A sentence mentioned by a join is mentioned by one of its members.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mentionedBy_join {n : ℕ} {ts : List (Strategy n)} {φ : Sentence}
    (h : MentionedBy (Strategy.join ts) φ) : ∃ T ∈ ts, MentionedBy T φ := by
  rcases h with ⟨e, he⟩ | ⟨p, hp, k, hk⟩
  · change (e, φ) ∈ ts.flatMap Strategy.trades at he
    rw [List.mem_flatMap] at he
    obtain ⟨T, hT, he⟩ := he
    exact ⟨T, hT, Or.inl ⟨e, he⟩⟩
  · change p ∈ ts.flatMap Strategy.trades at hp
    rw [List.mem_flatMap] at hp
    obtain ⟨T, hT, hp⟩ := hp
    exact ⟨T, hT, Or.inr ⟨p, hp, k, hk⟩⟩

/-- A sentence mentioned by a member of a join is mentioned by the join.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mentionedBy_join_of {n : ℕ} {ts : List (Strategy n)} {T : Strategy n} (hT : T ∈ ts)
    {φ : Sentence} (h : MentionedBy T φ) : MentionedBy (Strategy.join ts) φ := by
  rcases h with ⟨e, he⟩ | ⟨p, hp, k, hk⟩
  · refine Or.inl ⟨e, ?_⟩
    change (e, φ) ∈ ts.flatMap Strategy.trades
    rw [List.mem_flatMap]
    exact ⟨T, hT, he⟩
  · refine Or.inr ⟨p, ?_, k, hk⟩
    change p ∈ ts.flatMap Strategy.trades
    rw [List.mem_flatMap]
    exact ⟨T, hT, hp⟩

/-- A sentence mentioned by a scaled strategy is mentioned by the strategy or is a leaf of the
scaling feature.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mentionedBy_scaleBy {n : ℕ} {e : LogicalInduction.EF} {he : e.rank ≤ n} {T : Strategy n}
    {φ : Sentence} (h : MentionedBy (T.scaleBy e he) φ) :
    MentionedBy T φ ∨ ∃ k, (k, φ) ∈ e.priceQueries := by
  rcases h with ⟨f, hf⟩ | ⟨p, hp, k, hk⟩
  · change (f, φ) ∈ T.trades.map (fun p => (LogicalInduction.EF.mul e p.1, p.2)) at hf
    rw [List.mem_map] at hf
    obtain ⟨q, hq, hq'⟩ := hf
    have : q.2 = φ := (Prod.mk.inj hq').2
    exact Or.inl (Or.inl ⟨q.1, by rw [← this]; exact hq⟩)
  · change p ∈ T.trades.map (fun p => (LogicalInduction.EF.mul e p.1, p.2)) at hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    simp only [LogicalInduction.EF.priceQueries, List.mem_append] at hk
    rcases hk with hk | hk
    · exact Or.inr ⟨k, hk⟩
    · exact Or.inl (Or.inr ⟨q, hq, k, hk⟩)

/-- Scaling by a constant preserves the mentioned set (downwards).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mentionedBy_scaleConst {n : ℕ} {q : ℚ} {T : Strategy n} {φ : Sentence}
    (h : MentionedBy (T.scaleConst q) φ) : MentionedBy T φ := by
  unfold Strategy.scaleConst at h
  rcases mentionedBy_scaleBy h with h | ⟨k, hk⟩
  · exact h
  · simp [LogicalInduction.EF.priceQueries] at hk

/-- Scaling by a constant preserves the mentioned set (upwards).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mentionedBy_scaleConst_of {n : ℕ} {q : ℚ} {T : Strategy n} {φ : Sentence}
    (h : MentionedBy T φ) : MentionedBy (T.scaleConst q) φ := by
  rcases h with ⟨e, he⟩ | ⟨p, hp, k, hk⟩
  · refine Or.inl ⟨LogicalInduction.EF.mul (.const q) e, ?_⟩
    change (LogicalInduction.EF.mul (.const q) e, φ) ∈
      T.trades.map (fun p => (LogicalInduction.EF.mul (.const q) p.1, p.2))
    rw [List.mem_map]
    exact ⟨(e, φ), he, rfl⟩
  · refine Or.inr ⟨(LogicalInduction.EF.mul (.const q) p.1, p.2), ?_, k, ?_⟩
    · change (LogicalInduction.EF.mul (.const q) p.1, p.2) ∈
        T.trades.map (fun p => (LogicalInduction.EF.mul (.const q) p.1, p.2))
      rw [List.mem_map]
      exact ⟨p, hp, rfl⟩
    · simp [LogicalInduction.EF.priceQueries, hk]

/-- The empty strategy mentions nothing.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma not_mentionedBy_nil {n : ℕ} {φ : Sentence} {h0 : ∀ p ∈ ([] : List (EF × Sentence)), p.1.rank ≤ n}
    (h : MentionedBy (⟨[], h0⟩ : Strategy n) φ) : False := by
  rcases h with ⟨e, he⟩ | ⟨p, hp, _⟩
  · exact List.not_mem_nil he
  · exact List.not_mem_nil hp

/-- Leaves of a `sumFeatures` are leaves of a summand.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_priceQueries_sumFeatures {es : List LogicalInduction.EF} {k : ℕ} {φ : Sentence}
    (h : (k, φ) ∈ (ROIBudget.sumFeatures es).priceQueries) :
    ∃ e ∈ es, (k, φ) ∈ e.priceQueries := by
  induction es with
  | nil => simp [ROIBudget.sumFeatures, LogicalInduction.EF.priceQueries] at h
  | cons e es ih =>
      change (k, φ) ∈ (LogicalInduction.EF.add e (ROIBudget.sumFeatures es)).priceQueries at h
      simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
      rcases h with h | h
      · exact ⟨e, by simp, h⟩
      · obtain ⟨e', he', hk⟩ := ih h
        exact ⟨e', by simp [he'], hk⟩

/-- Leaves of `EF.neg` are leaves of the argument.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_priceQueries_neg {e : LogicalInduction.EF} {k : ℕ} {φ : Sentence}
    (h : (k, φ) ∈ (LogicalInduction.EF.neg e).priceQueries) : (k, φ) ∈ e.priceQueries := by
  simpa [LogicalInduction.EF.neg, LogicalInduction.EF.priceQueries] using h

/-- Leaves of `EF.min` are leaves of an argument.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_priceQueries_min {a b : LogicalInduction.EF} {k : ℕ} {φ : Sentence}
    (h : (k, φ) ∈ (LogicalInduction.EF.min a b).priceQueries) :
    (k, φ) ∈ a.priceQueries ∨ (k, φ) ∈ b.priceQueries := by
  simpa [LogicalInduction.EF.min, LogicalInduction.EF.neg, LogicalInduction.EF.priceQueries]
    using h

/-- Leaves of `EF.listMin` are leaves of a member.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_priceQueries_listMin {es : List LogicalInduction.EF} {k : ℕ} {φ : Sentence}
    (h : (k, φ) ∈ (LogicalInduction.EF.listMin es).priceQueries) :
    ∃ e ∈ es, (k, φ) ∈ e.priceQueries := by
  induction es with
  | nil => simp [LogicalInduction.EF.listMin, LogicalInduction.EF.priceQueries] at h
  | cons e es ih =>
      change (k, φ) ∈ (LogicalInduction.EF.min e (LogicalInduction.EF.listMin es)).priceQueries at h
      rcases mem_priceQueries_min h with h | h
      · exact ⟨e, by simp, h⟩
      · obtain ⟨e', he', hk⟩ := ih h
        exact ⟨e', by simp [he'], hk⟩

/-- Leaves of a strategy's `worldValueFeature` are mentioned by the strategy (its coefficients'
leaves and the day-`n` prices of its traded sentences).
Source: [[bli-overlay-mandate]] T2 step (1); Known issue 4
Kind: L
Fidelity: n/a -/
lemma mem_priceQueries_worldValueFeature {n : ℕ} {T : Strategy n} {u : ℕ → Bool} {k : ℕ}
    {φ : Sentence} (h : (k, φ) ∈ (T.worldValueFeature u).priceQueries) : MentionedBy T φ := by
  unfold Strategy.worldValueFeature at h
  obtain ⟨e, he, hk⟩ := mem_priceQueries_sumFeatures h
  rw [List.mem_map] at he
  obtain ⟨p, hp, rfl⟩ := he
  simp only [LogicalInduction.EF.priceQueries, List.mem_append, List.mem_singleton,
    List.nil_append, Prod.mk.injEq] at hk
  rcases hk with hk | ⟨_, rfl⟩
  · exact mentionedBy_of_mem_priceQueries hp hk
  · exact mentionedBy_of_mem_trades hp

/-- Leaves of one budget world scale are mentioned by the raw day strategy.
Source: [[bli-overlay-mandate]] T2 step (1)
Kind: L
Fidelity: n/a -/
lemma mem_priceQueries_budgetWorldScale {Tr : Trader} {b : ℕ} {Q : ℕ → Sentence → ℚ}
    {u : ℕ → Bool} {n k : ℕ} {φ : Sentence}
    (h : (k, φ) ∈ (budgetWorldScale Tr b Q u n).priceQueries) : MentionedBy (Tr.strat n) φ := by
  unfold budgetWorldScale at h
  simp only [LogicalInduction.EF.priceQueries, List.nil_append] at h
  exact mem_priceQueries_worldValueFeature (mem_priceQueries_neg h)

/-- Leaves of the budget scale feature are mentioned by the raw day strategy: the budgeter reads
the table `Q` and the stages as **data** (`rawPriorWorthRat`, `priorBudgetBreach`,
`budgetAtoms`), never as price leaves.
Source: [[bli-overlay-mandate]] T2 step (1); Known issue 4
Kind: L
Fidelity: n/a -/
lemma mem_priceQueries_budgetScaleFeature {DP : DeductiveProcess} {Tr : Trader} {b : ℕ}
    {Q : ℕ → Sentence → ℚ} {n k : ℕ} {φ : Sentence}
    (h : (k, φ) ∈ (budgetScaleFeature DP Tr b Q n).priceQueries) :
    MentionedBy (Tr.strat n) φ := by
  unfold budgetScaleFeature at h
  obtain ⟨e, he, hk⟩ := mem_priceQueries_listMin h
  rw [List.mem_map] at he
  obtain ⟨bits, _, rfl⟩ := he
  exact mem_priceQueries_budgetWorldScale hk

/-- The budgeted day action mentions only what the raw day strategy mentions.
Source: [[bli-overlay-mandate]] T2 step (1)
Kind: L
Fidelity: n/a -/
lemma mentionedBy_BudgeterAt {DP : DeductiveProcess} {Tr : Trader} {b : ℕ}
    {Q : ℕ → Sentence → ℚ} {n : ℕ} {φ : Sentence}
    (h : MentionedBy (BudgeterAt DP Tr b Q n) φ) : MentionedBy (Tr.strat n) φ := by
  unfold BudgeterAt at h
  split_ifs at h with hb
  · exact absurd h not_mentionedBy_nil
  · rcases mentionedBy_scaleBy h with h | ⟨k, hk⟩
    · exact h
    · exact mem_priceQueries_budgetScaleFeature hk

/-- One enumeration component mentions only what its raw (gated) trader mentions on the day.
Source: [[bli-overlay-mandate]] T2 step (1)
Kind: L
Fidelity: n/a -/
lemma mentionedBy_tradingFirmComponentAt {DP : DeductiveProcess} {Q : ℕ → Sentence → ℚ}
    {n j : ℕ} {φ : Sentence} (h : MentionedBy (tradingFirmComponentAt DP Q n j) φ) :
    MentionedBy ((firmRawTrader j).strat n) φ := by
  unfold tradingFirmComponentAt at h
  obtain ⟨T, hT, hTφ⟩ := mentionedBy_join h
  rw [List.mem_append, List.mem_singleton] at hT
  rcases hT with hT | rfl
  · unfold tradingFirmBudgetComponents at hT
    rw [List.mem_map] at hT
    obtain ⟨r, _, rfl⟩ := hT
    exact mentionedBy_BudgeterAt (mentionedBy_scaleConst hTφ)
  · exact mentionedBy_scaleConst hTφ

/-- **T2 step (1), downwards.** The firm's day-`n` strategy mentions only sentences mentioned by
some enumerated raw trader `j ≤ n` on day `n`.
Source: [[bli-overlay-mandate]] T2 step (1)
Kind: L
Fidelity: exact -/
theorem mentionedBy_TradingFirmAt {DP : DeductiveProcess} {Q : ℕ → Sentence → ℚ} {n : ℕ}
    {φ : Sentence} (h : MentionedBy (TradingFirmAt DP Q n) φ) :
    ∃ j ≤ n, MentionedBy ((enumeratedTrader j).strat n) φ := by
  unfold TradingFirmAt at h
  obtain ⟨T, hT, hTφ⟩ := mentionedBy_join h
  rw [List.mem_map] at hT
  obtain ⟨j, hj, rfl⟩ := hT
  rw [List.mem_range] at hj
  have hjn : j ≤ n := Nat.lt_succ_iff.mp hj
  refine ⟨j, hjn, ?_⟩
  have h2 := mentionedBy_tradingFirmComponentAt hTφ
  unfold firmRawTrader at h2
  rw [Trader.gate_strat_of_le _ hjn] at h2
  exact h2

/-- **T2 step (1), upwards.** Whatever an enumerated raw trader `j ≤ n` mentions on day `n`,
the firm's day-`n` strategy mentions (through the tail component `scaleConst` of index `j`).
Source: [[bli-overlay-mandate]] T2 step (1); T2 witness
Kind: L
Fidelity: exact -/
theorem mentionedBy_TradingFirmAt_of_raw {DP : DeductiveProcess} {Q : ℕ → Sentence → ℚ}
    {n j : ℕ} (hj : j ≤ n) {φ : Sentence} (h : MentionedBy ((enumeratedTrader j).strat n) φ) :
    MentionedBy (TradingFirmAt DP Q n) φ := by
  have hraw : MentionedBy ((firmRawTrader j).strat n) φ := by
    unfold firmRawTrader
    rw [Trader.gate_strat_of_le _ hj]
    exact h
  unfold TradingFirmAt
  apply mentionedBy_join_of (T := tradingFirmComponentAt DP Q n j)
  · rw [List.mem_map]
    exact ⟨j, List.mem_range.mpr (Nat.lt_succ_of_le hj), rfl⟩
  · unfold tradingFirmComponentAt
    apply mentionedBy_join_of
      (T := ((firmRawTrader j).strat n).scaleConst (tradingFirmWeight j (tradingFirmCutoff n)))
    · simp
    · exact mentionedBy_scaleConst_of hraw

/-- **The firm's mentioned set, characterised** (Known issue 5): it is the union over the open
indices `j ≤ n` of the enumerated raw traders' day-`n` mentioned sets, and does not depend on
the process `DP` or the table `Q`.
Source: [[bli-overlay-mandate]] T2 step (1); Known issue 5
Kind: L
Fidelity: exact -/
theorem mentionedBy_TradingFirmAt_iff (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ) (n : ℕ)
    (φ : Sentence) :
    MentionedBy (TradingFirmAt DP Q n) φ ↔ ∃ j ≤ n, MentionedBy ((enumeratedTrader j).strat n) φ :=
  ⟨mentionedBy_TradingFirmAt, fun ⟨_, hj, h⟩ => mentionedBy_TradingFirmAt_of_raw hj h⟩

/-- The firm's mentioned set is independent of the process and the table.
Source: [[bli-overlay-mandate]] Known issue 5
Kind: L
Fidelity: exact -/
theorem mentionedSet_TradingFirmAt_eq (DP DP' : DeductiveProcess) (Q Q' : ℕ → Sentence → ℚ)
    (n : ℕ) : mentionedSet (TradingFirmAt DP Q n) = mentionedSet (TradingFirmAt DP' Q' n) := by
  ext φ
  rw [mem_mentionedSet_iff, mem_mentionedSet_iff, mentionedBy_TradingFirmAt_iff,
    mentionedBy_TradingFirmAt_iff]

/-! ## Step 2: size per enumeration index -/

/-- The machine token stream of index `j` on day `n` is the digit stream of some output word
(`[]` on timeout, the halted machine's coded output otherwise).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma machineTokens_eq_bitsToDigits (j n : ℕ) : ∃ w : List Bool, machineTokens j n = bitsToDigits w := by
  unfold machineTokens
  cases evalHalted (progDesc j) (progClock j n) (unaryDay n) with
  | none => exact ⟨[], by simp [tokensOf, bitsToDigits]⟩
  | some c => exact ⟨codedOutput c, rfl⟩

/-- **T2 step (2).** Every sentence mentioned by enumerated raw trader `j` on day `n` has size at
most `2^((C+6)(progClock j n + 1))`, `C` the structured-escape constant: bli-found's
`tokenSize_le_bridgeBound_of_mentionedBy` at the machine's output word, the token count
bounded by the index's clock (`length_machineTokens_le`), and `bridgeBound_le`.
Source: [[bli-overlay-mandate]] T2 step (2)
Kind: C
Fidelity: exact -/
theorem tokenSize_le_of_mentionedBy_enumerated {C : ℕ}
    (hC : ∀ (ts : List ℕ) (φ : Sentence) (rest : List ℕ),
      parseStructuredPaperPrime ts = some (φ, rest) →
        tokenSize φ ≤ 2 ^ (C * (ts.length - rest.length)) + C)
    {j n : ℕ} {φ : Sentence} (h : MentionedBy ((enumeratedTrader j).strat n) φ) :
    tokenSize φ ≤ 2 ^ ((C + 6) * (progClock j n + 1)) := by
  obtain ⟨w, hw⟩ := machineTokens_eq_bitsToDigits j n
  have h' : MentionedBy (strategyOfOutput n w) φ := by
    rw [enumeratedTrader_strat, hw] at h
    exact h
  have h1 := tokenSize_le_bridgeBound_of_mentionedBy hC h'
  have h2 : (bitsToDigits w).length ≤ progClock j n := by
    rw [← hw]
    exact length_machineTokens_le j n
  calc tokenSize φ ≤ bridgeBound C (bitsToDigits w).length := h1
    _ ≤ bridgeBound C (progClock j n) := bridgeBound_mono C h2
    _ ≤ 2 ^ ((C + 6) * (progClock j n + 1)) := bridgeBound_le C _

/-! ## Step 3: arithmetic — the square-root bounds on `Nat.unpair` -/

/-- The first component of `Nat.unpair m` is at most `Nat.sqrt m`.
Source: [[bli-overlay-mandate]] T2 step (3)
Kind: L
Fidelity: n/a -/
lemma unpair_fst_le_sqrt (m : ℕ) : (Nat.unpair m).1 ≤ Nat.sqrt m := by
  unfold Nat.unpair
  dsimp only
  split_ifs with h
  · exact h.le
  · exact le_rfl

/-- The second component of `Nat.unpair m` is at most `Nat.sqrt m`.
Source: [[bli-overlay-mandate]] T2 step (3)
Kind: L
Fidelity: n/a -/
lemma unpair_snd_le_sqrt (m : ℕ) : (Nat.unpair m).2 ≤ Nat.sqrt m := by
  unfold Nat.unpair
  dsimp only
  split_ifs with h
  · exact le_rfl
  · have := Nat.sqrt_le_add m
    omega

/-- The clock coefficient of index `j` is at most `Nat.sqrt j`.
Source: [[bli-overlay-mandate]] T2 step (3)
Kind: L
Fidelity: n/a -/
lemma progCoeff_le_sqrt (j : ℕ) : progCoeff j ≤ Nat.sqrt j := by
  unfold progCoeff
  calc (Nat.unpair (Nat.unpair j).1).2 ≤ Nat.sqrt (Nat.unpair j).1 := unpair_snd_le_sqrt _
    _ ≤ Nat.sqrt j := Nat.sqrt_le_sqrt (Nat.unpair_left_le j)

/-- The clock degree of index `j` is at most `Nat.sqrt j`.
Source: [[bli-overlay-mandate]] T2 step (3)
Kind: L
Fidelity: n/a -/
lemma progDeg_le_sqrt (j : ℕ) : progDeg j ≤ Nat.sqrt j := unpair_snd_le_sqrt j

/-- The clock of an open index `j ≤ n` on day `n` is at most `√n · (n+1)^{√n} + √n`.
Source: [[bli-overlay-mandate]] T2 step (3)
Kind: L
Fidelity: n/a -/
lemma progClock_le {j n : ℕ} (hj : j ≤ n) :
    progClock j n ≤ Nat.sqrt n * (n + 1) ^ Nat.sqrt n + Nat.sqrt n := by
  unfold progClock
  have ha : progCoeff j ≤ Nat.sqrt n := (progCoeff_le_sqrt j).trans (Nat.sqrt_le_sqrt hj)
  have hd : progDeg j ≤ Nat.sqrt n := (progDeg_le_sqrt j).trans (Nat.sqrt_le_sqrt hj)
  have hpow : (n + 1) ^ progDeg j ≤ (n + 1) ^ Nat.sqrt n :=
    Nat.pow_le_pow_right (by omega) hd
  exact Nat.add_le_add (Nat.mul_le_mul ha hpow) ha

/-- `4 (s+1)^2 ≤ 2^s` from `s = 9` on.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma four_mul_sq_le_two_pow {s : ℕ} (hs : 9 ≤ s) : 4 * (s + 1) ^ 2 ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
      rw [pow_succ 2 s]
      have : (s + 1 + 1) ^ 2 ≤ 2 * (s + 1) ^ 2 := by nlinarith
      nlinarith

/-- **T2 step (3), the estimate.** For `n ≥ (C+16)^2` and every open index `j ≤ n`,
`(C+6)(progClock j n + 1) ≤ 2^n`. With `s = √n`: the clock is `≤ s (n+1)^s + s`,
`4(n+1) ≤ 4(s+1)^2 ≤ 2^s`, so `4^s (n+1)^s ≤ 2^{s²} ≤ 2^n`, and `(C+6)(2s+1) ≤ 4^s`.
Source: [[bli-overlay-mandate]] T2 step (3); Known issue 1
Kind: P
Fidelity: exact -/
theorem firmClock_arith (C : ℕ) :
    ∀ n ≥ (C + 16) ^ 2, ∀ j ≤ n, (C + 6) * (progClock j n + 1) ≤ 2 ^ n := by
  intro n hn j hj
  have hs_ge : C + 16 ≤ Nat.sqrt n := by
    rw [← Nat.sqrt_eq' (C + 16)]
    exact Nat.sqrt_le_sqrt hn
  have hclock := progClock_le hj
  have hn_lt : n < (Nat.sqrt n + 1) ^ 2 := Nat.lt_succ_sqrt' n
  have hss : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  set s := Nat.sqrt n with hs
  have hs9 : 9 ≤ s := by omega
  have hsq : 4 * (s + 1) ^ 2 ≤ 2 ^ s := four_mul_sq_le_two_pow hs9
  have hsp : s + 1 ≤ (s + 1) ^ 2 := by nlinarith
  have h1 : 4 * (n + 1) ≤ 2 ^ s := by nlinarith
  have h2 : (4 * (n + 1)) ^ s ≤ 2 ^ n := by
    calc (4 * (n + 1)) ^ s ≤ (2 ^ s) ^ s := Nat.pow_le_pow_left h1 s
      _ = 2 ^ (s * s) := by rw [← pow_mul]
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hss
  have hpow1 : 1 ≤ (n + 1) ^ s := Nat.one_le_pow _ _ (by omega)
  have hpow1' : (s + 1) * 1 ≤ (s + 1) * (n + 1) ^ s := Nat.mul_le_mul_left _ hpow1
  have h3 : progClock j n + 1 ≤ (2 * s + 1) * (n + 1) ^ s := by nlinarith
  have h4 : (C + 6) * (2 * s + 1) ≤ 4 ^ s := by
    have hC : C + 6 ≤ 2 ^ s := by nlinarith
    have h2s : 2 * s + 1 ≤ 2 ^ s := by nlinarith
    calc (C + 6) * (2 * s + 1) ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul hC h2s
      _ = 4 ^ s := by rw [← mul_pow]; norm_num
  calc (C + 6) * (progClock j n + 1) ≤ (C + 6) * ((2 * s + 1) * (n + 1) ^ s) :=
        Nat.mul_le_mul_left _ h3
    _ = ((C + 6) * (2 * s + 1)) * (n + 1) ^ s := by ring
    _ ≤ 4 ^ s * (n + 1) ^ s := Nat.mul_le_mul_right _ h4
    _ = (4 * (n + 1)) ^ s := by rw [mul_pow]
    _ ≤ 2 ^ n := h2

/-! ## T2: the firm-support lemma -/

/-- **T2 with the constant exposed.** For the structured-escape constant `C`, from day
`(C+16)^2` on the firm's day-`n` strategy mentions only day-`n`-small sentences, for every
process and every table.
Source: [[bli-overlay-mandate]] T2
Kind: C
Fidelity: exact
Hyps: (a) — `hC` is `tokenSize_le_of_structured`'s conclusion (proved in bli-found), passed explicitly to expose `C` -/
theorem firm_mentioned_small_from {C : ℕ}
    (hC : ∀ (ts : List ℕ) (φ : Sentence) (rest : List ℕ),
      parseStructuredPaperPrime ts = some (φ, rest) →
        tokenSize φ ≤ 2 ^ (C * (ts.length - rest.length)) + C) :
    ∀ n ≥ (C + 16) ^ 2, ∀ (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ) (φ : Sentence),
      MentionedBy (TradingFirmAt DP Q n) φ → SmallOn n φ := by
  intro n hn DP Q φ hφ
  obtain ⟨j, hj, hφj⟩ := mentionedBy_TradingFirmAt hφ
  have hsize := tokenSize_le_of_mentionedBy_enumerated hC hφj
  unfold SmallOn sizeBound
  exact hsize.trans (Nat.pow_le_pow_right (by norm_num) (firmClock_arith C n hn j hj))

/-- **T2 (F2). The firm-support lemma.** From some day `N₀` on, every sentence mentioned by FAF's
trading firm's day-`n` strategy `TradingFirmAt DP Q n` — traded, or a price leaf of one of its
coefficients — is small on day `n`, uniformly in the process `DP` and the table `Q` (the
overlaid table included). `N₀ = (C+16)^2` for the structured-escape constant `C`.
Source: [[bli-program]] §2.1 (F2), §4 row F2; [[bli-overlay-mandate]] T2
Kind: C
Fidelity: exact
Hyps: (a) — nothing assumed; `tokenSize_le_of_structured`, `tokenSize_le_bridgeBound_of_mentionedBy`, `length_machineTokens_le` and the `Nat.unpair` bounds are all proved -/
theorem firm_mentioned_small :
    ∃ N₀, ∀ n ≥ N₀, ∀ (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ) (φ : Sentence),
      MentionedBy (TradingFirmAt DP Q n) φ → SmallOn n φ := by
  obtain ⟨C, hC⟩ := tokenSize_le_of_structured
  exact ⟨(C + 16) ^ 2, firm_mentioned_small_from hC⟩

/-- **T2, finite-set form.** From `N₀` on, `mentionedSet (TradingFirmAt DP Q n) ⊆ smallSet n`.
Source: [[bli-program]] §3.3 (i); [[bli-overlay-mandate]] T2
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem firm_mentionedSet_subset_smallSet :
    ∃ N₀, ∀ n ≥ N₀, ∀ (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ),
      mentionedSet (TradingFirmAt DP Q n) ⊆ smallSet n := by
  obtain ⟨N₀, hN⟩ := firm_mentioned_small
  refine ⟨N₀, fun n hn DP Q φ hφ => ?_⟩
  rw [mem_smallSet]
  exact hN n hn DP Q φ ((mem_mentionedSet_iff _ φ).mp hφ)

/-- **T2, the plan's wording** (Known issue 2: the support form is the weaker corollary).
Source: [[bli-program]] §4 row F2; [[bli-overlay-mandate]] T2, Known issue 2
Kind: C
Fidelity: weaker: traded sentences only (the mentioned-set form above is the headline) -/
theorem firm_support_subset_smallSet :
    ∃ N₀, ∀ n ≥ N₀, ∀ (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ),
      (TradingFirmAt DP Q n).support ⊆ smallSet n := by
  obtain ⟨N₀, hN⟩ := firm_mentionedSet_subset_smallSet
  exact ⟨N₀, fun n hn DP Q =>
    (support_subset_mentionedSet _).trans (hN n hn DP Q)⟩

/-! ## The witness: the firm mentions something -/

/-- **T2 witness (N+).** The firm's mentioned set is not empty: FAF's e.c. trader `buyAtomDaily`
(which trades `⌜aₙ⌝` on day `n`) has an enumeration index `j` (`exists_enumeratedTrader_eq`),
and on every day `n ≥ j`, for every process and every table, the firm mentions `⌜aₙ⌝`. The day
is `n ≥ j` for the (non-constructive) index `j`; the sentence varies with the day.
Source: [[bli-overlay-mandate]] T2 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem firm_mentions_something :
    ∃ j, ∀ n ≥ j, ∀ (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ),
      MentionedBy (TradingFirmAt DP Q n) (Formula.atom n) := by
  obtain ⟨j, hj⟩ := exists_enumeratedTrader_eq buyAtomDaily efficientlyComputable_buyAtomDaily
  refine ⟨j, fun n hn DP Q => ?_⟩
  apply mentionedBy_TradingFirmAt_of_raw hn
  rw [hj]
  exact buyAtomDaily_mentions n

/-- The witness in finite-set form: `mentionedSet (TradingFirmAt DP Q n)` is nonempty from day
`j` on.
Source: [[bli-overlay-mandate]] T2 (witness)
Kind: N+
Fidelity: n/a -/
theorem firm_mentionedSet_nonempty :
    ∃ j, ∀ n ≥ j, ∀ (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ),
      (mentionedSet (TradingFirmAt DP Q n)).Nonempty := by
  obtain ⟨j, hj⟩ := firm_mentions_something
  exact ⟨j, fun n hn DP Q => ⟨Formula.atom n, (mem_mentionedSet_iff _ _).mpr (hj n hn DP Q)⟩⟩

end Cleanroom.Bli.BliOverlay.AttemptB
