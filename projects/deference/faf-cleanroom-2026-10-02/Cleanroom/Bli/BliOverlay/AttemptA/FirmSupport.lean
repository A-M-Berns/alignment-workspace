import Cleanroom.Bli.BliOverlay.AttemptA.Mentioned
import Cleanroom.Bli.BliFound.Witnesses
import LogicalInduction.Construction.TradingFirm

/-!
# `bli-overlay` (attempt A) · FirmSupport: the firm-support lemma (F2, T2)

**The claim (T2, headline).** From some day `N₀` on, every sentence the trading firm's day-`n`
strategy mentions — traded, or read at a price leaf of one of its coefficients — is small on day
`n`: `firm_mentioned_small : ∃ N₀, ∀ n ≥ N₀, ∀ DP Q φ, MentionedBy (TradingFirmAt DP Q n) φ →
SmallOn n φ`, uniform in the process `DP` and the rational table `Q` the firm is built from.
Corollaries: the `mentionedSet` and the `support` inclusions into `smallSet n`.

**Route (all derived).**

1. *Structure* (`mentionedBy_TradingFirmAt`): the firm's day-`n` strategy is a `Strategy.join`
   over indices `j ≤ n` of components, each a join of budgeted copies (`BudgeterAt`, zero or
   `scaleBy` a `budgetScaleFeature`) and one `scaleConst`ed copy of the gated enumerated trader
   `(enumeratedTrader j).strat n`. Scaling multiplies coefficients by a feature, so a mentioned
   sentence is either traded by the raw strategy or a price leaf of the scaling feature; the
   budget feature is a `listMin` of `safeRecip`s of `worldValueFeature`s, whose leaves are the raw
   strategy's own coefficient leaves and `price φ n` for its traded `φ`. Hence
   `mentionedSet (TradingFirmAt DP Q n) = ⋃_{j ≤ n} mentionedSet ((enumeratedTrader j).strat n)`
   (`mentionedSet_TradingFirmAt_eq`): independent of `DP` and `Q` (Known issue 5) — the budgeter
   reads `Q` and `DP` as *data* (`rawPriorWorthRat`, `priorBudgetBreach`, `budgetAtoms`), never as
   leaves.
2. *Size per index* (`tokenSize_le_of_mentionedBy_enumerated`): `(enumeratedTrader j).strat n`
   is `strategyOfOutput n w` for the machine's output word `w` (or `[]` on timeout), whose digit
   stream has length `≤ progClock j n` (FAF's `length_machineTokens_le`); `bli-found`'s
   `tokenSize_le_bridgeBound_of_mentionedBy` and `bridgeBound_le` give
   `tokenSize φ ≤ 2 ^ ((C + 6) · (progClock j n + 1))` with `C` the structured constant.
3. *Arithmetic* (`eventually_firm_clock_le`): `(C + 6)(progClock j n + 1) ≤ 2 ^ n` for all
   `j ≤ n` from `N₀ = 2^10 + 4C + 32` on. The crude bounds `progCoeff j, progDeg j ≤ j` do **not**
   suffice (mandate T2 step 3): the degree must be bounded by `Nat.sqrt n`, which holds because
   `Nat.unpair` returns components `≤ Nat.sqrt` of its input (`unpair_snd_le_sqrt`). With
   `s = √n`, `l = log₂ n`: `progClock j n + 1 ≤ 2 (n+1)^{s+1} ≤ 2^{1 + (l+1)(s+1)}`, and
   `C + 7 + (l+1)(s+1) ≤ n` once `2(l+1) ≤ s` (from `4 (l+1)^2 ≤ 2^l ≤ n`, `l ≥ 10`) and
   `4C + 32 ≤ n`.

**Witness (N+, `firm_mentions_something`).** For every `DP` and `Q` and every day `n` at or after
the enumeration index `i` of FAF's `buyAtomDaily` (`exists_enumeratedTrader_eq`), the firm's
day-`n` strategy mentions `⌜aₙ⌝`; the index `i` is existential (a non-constructive day is still a
day). The `paperDP 𝗜𝚺₁` instance is in `Witness.lean`.

Sources: [[bli-overlay-mandate]] T2 and Known issues 1, 2, 5; [[bli-program]] §2.1 (F2), §4 row F2.
-/

namespace Cleanroom.Bli.BliOverlay.AttemptA

open LogicalInduction LogicalInduction.MachineExec LO.Propositional Cleanroom.Bli.BliFound

/-! ## Step 1: leaves of the budgeter's features -/

/-- Leaves of `ROIBudget.sumFeatures es` are leaves of members of `es`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_priceQueries_sumFeatures {es : List EF} {q : ℕ × Sentence}
    (h : q ∈ (ROIBudget.sumFeatures es).priceQueries) : ∃ e ∈ es, q ∈ e.priceQueries := by
  induction es with
  | nil => simp [ROIBudget.sumFeatures, EF.priceQueries] at h
  | cons e es ih =>
      have h' : q ∈ (EF.add e (ROIBudget.sumFeatures es)).priceQueries := h
      simp only [EF.priceQueries, List.mem_append] at h'
      rcases h' with h1 | h1
      · exact ⟨e, List.mem_cons_self, h1⟩
      · obtain ⟨e', he', hq⟩ := ih h1
        exact ⟨e', List.mem_cons_of_mem _ he', hq⟩

/-- Leaves of `EF.min a b` are leaves of `a` or of `b`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_priceQueries_min {a b : EF} {q : ℕ × Sentence}
    (h : q ∈ (EF.min a b).priceQueries) : q ∈ a.priceQueries ∨ q ∈ b.priceQueries := by
  simpa [EF.min, EF.neg, EF.priceQueries] using h

/-- Leaves of `EF.listMin es` are leaves of members of `es`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_priceQueries_listMin {es : List EF} {q : ℕ × Sentence}
    (h : q ∈ (EF.listMin es).priceQueries) : ∃ e ∈ es, q ∈ e.priceQueries := by
  induction es with
  | nil => simp [EF.listMin, EF.priceQueries] at h
  | cons e es ih =>
      have h' : q ∈ (EF.min e (EF.listMin es)).priceQueries := h
      rcases mem_priceQueries_min h' with h1 | h1
      · exact ⟨e, List.mem_cons_self, h1⟩
      · obtain ⟨e', he', hq⟩ := ih h1
        exact ⟨e', List.mem_cons_of_mem _ he', hq⟩

/-- A leaf of `T.worldValueFeature u` names a sentence `T` mentions: a coefficient leaf, or
`price φ n` for a traded `φ` (Known issue 4: the firm's coefficients do carry day-`n` leaves of
its traded sentences).
Source: [[bli-overlay-mandate]] T2 step 1; Known issue 4
Kind: L
Fidelity: n/a -/
lemma mentionedBy_of_mem_priceQueries_worldValueFeature {n : ℕ} (T : Strategy n)
    (u : ℕ → Bool) {k : ℕ} {φ : Sentence}
    (h : (k, φ) ∈ (T.worldValueFeature u).priceQueries) : MentionedBy T φ := by
  unfold Strategy.worldValueFeature at h
  obtain ⟨e, he, hq⟩ := mem_priceQueries_sumFeatures h
  simp only [List.mem_map] at he
  obtain ⟨p, hp, rfl⟩ := he
  simp only [EF.priceQueries, List.mem_append, List.nil_append, List.mem_singleton,
    Prod.mk.injEq] at hq
  rcases hq with hq | ⟨_, rfl⟩
  · exact Or.inr ⟨p, hp, k, hq⟩
  · exact Or.inl ⟨p.1, hp⟩

/-- A leaf of `budgetWorldScale Tr b Q u n` names a sentence `Tr.strat n` mentions.
Source: [[bli-overlay-mandate]] T2 step 1
Kind: L
Fidelity: n/a -/
lemma mentionedBy_of_mem_priceQueries_budgetWorldScale (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (u : ℕ → Bool) (n : ℕ) {k : ℕ} {φ : Sentence}
    (h : (k, φ) ∈ (budgetWorldScale Tr b Q u n).priceQueries) : MentionedBy (Tr.strat n) φ := by
  unfold budgetWorldScale at h
  simp only [EF.priceQueries, EF.neg, List.nil_append] at h
  exact mentionedBy_of_mem_priceQueries_worldValueFeature _ _ h

/-- A leaf of `budgetScaleFeature DP Tr b Q n` names a sentence `Tr.strat n` mentions: `DP` and
`Q` enter the feature as data (the world enumeration and `rawPriorWorthRat`), not as leaves.
Source: [[bli-overlay-mandate]] T2 step 1; Known issue 5
Kind: L
Fidelity: n/a -/
lemma mentionedBy_of_mem_priceQueries_budgetScaleFeature (DP : DeductiveProcess) (Tr : Trader)
    (b : ℕ) (Q : ℕ → Sentence → ℚ) (n : ℕ) {k : ℕ} {φ : Sentence}
    (h : (k, φ) ∈ (budgetScaleFeature DP Tr b Q n).priceQueries) :
    MentionedBy (Tr.strat n) φ := by
  unfold budgetScaleFeature at h
  dsimp only at h
  obtain ⟨e, he, hq⟩ := mem_priceQueries_listMin h
  simp only [List.mem_map] at he
  obtain ⟨bits, _, rfl⟩ := he
  exact mentionedBy_of_mem_priceQueries_budgetWorldScale _ _ _ _ _ hq

/-! ## Step 1: the strategy algebra -/

/-- A sentence mentioned by `T.scaleBy e` is mentioned by `T` or is a leaf of `e`.
Source: [[bli-overlay-mandate]] T2 step 1
Kind: L
Fidelity: n/a -/
lemma mentionedBy_scaleBy {n : ℕ} {e : EF} {he : e.rank ≤ n} {T : Strategy n} {φ : Sentence}
    (h : MentionedBy (T.scaleBy e he) φ) :
    MentionedBy T φ ∨ ∃ k, (k, φ) ∈ e.priceQueries := by
  rcases h with ⟨f, hf⟩ | ⟨p, hp, k, hk⟩
  · simp only [Strategy.scaleBy, List.mem_map, Prod.mk.injEq] at hf
    obtain ⟨q, hq, -, rfl⟩ := hf
    exact Or.inl (Or.inl ⟨q.1, hq⟩)
  · simp only [Strategy.scaleBy, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    simp only [EF.priceQueries, List.mem_append] at hk
    rcases hk with hk | hk
    · exact Or.inr ⟨k, hk⟩
    · exact Or.inl (Or.inr ⟨q, hq, k, hk⟩)

/-- Conversely, `T.scaleBy e` mentions everything `T` mentions.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mentionedBy_scaleBy_of {n : ℕ} (e : EF) (he : e.rank ≤ n) {T : Strategy n} {φ : Sentence}
    (h : MentionedBy T φ) : MentionedBy (T.scaleBy e he) φ := by
  rcases h with ⟨f, hf⟩ | ⟨p, hp, k, hk⟩
  · refine Or.inl ⟨EF.mul e f, ?_⟩
    simp only [Strategy.scaleBy, List.mem_map]
    exact ⟨(f, φ), hf, rfl⟩
  · refine Or.inr ⟨(EF.mul e p.1, p.2), ?_, k, ?_⟩
    · simp only [Strategy.scaleBy, List.mem_map]
      exact ⟨p, hp, rfl⟩
    · simp only [EF.priceQueries, List.mem_append]
      exact Or.inr hk

/-- `scaleConst` adds no leaves.
Source: [[bli-overlay-mandate]] T2 step 1
Kind: L
Fidelity: n/a -/
lemma mentionedBy_scaleConst {n : ℕ} {q : ℚ} {T : Strategy n} {φ : Sentence}
    (h : MentionedBy (T.scaleConst q) φ) : MentionedBy T φ := by
  unfold Strategy.scaleConst at h
  rcases mentionedBy_scaleBy h with h | ⟨k, hk⟩
  · exact h
  · simp [EF.priceQueries] at hk

/-- `scaleConst` keeps every mentioned sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mentionedBy_scaleConst_of {n : ℕ} (q : ℚ) {T : Strategy n} {φ : Sentence}
    (h : MentionedBy T φ) : MentionedBy (T.scaleConst q) φ :=
  mentionedBy_scaleBy_of _ _ h

/-- A sentence mentioned by a join is mentioned by a member.
Source: [[bli-overlay-mandate]] T2 step 1
Kind: L
Fidelity: n/a -/
lemma mentionedBy_join {n : ℕ} {ts : List (Strategy n)} {φ : Sentence}
    (h : MentionedBy (Strategy.join ts) φ) : ∃ T ∈ ts, MentionedBy T φ := by
  rcases h with ⟨e, he⟩ | ⟨p, hp, k, hk⟩
  · simp only [Strategy.join, List.mem_flatMap] at he
    obtain ⟨T, hT, he⟩ := he
    exact ⟨T, hT, Or.inl ⟨e, he⟩⟩
  · simp only [Strategy.join, List.mem_flatMap] at hp
    obtain ⟨T, hT, hp⟩ := hp
    exact ⟨T, hT, Or.inr ⟨p, hp, k, hk⟩⟩

/-- A join mentions everything a member mentions.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mentionedBy_join_of {n : ℕ} {ts : List (Strategy n)} {T : Strategy n} (hT : T ∈ ts)
    {φ : Sentence} (h : MentionedBy T φ) : MentionedBy (Strategy.join ts) φ := by
  rcases h with ⟨e, he⟩ | ⟨p, hp, k, hk⟩
  · exact Or.inl ⟨e, by simp only [Strategy.join, List.mem_flatMap]; exact ⟨T, hT, he⟩⟩
  · exact Or.inr ⟨p, by simp only [Strategy.join, List.mem_flatMap]; exact ⟨T, hT, hp⟩, k, hk⟩

/-- The budgeted copy of `Tr` on day `n` mentions only what `Tr.strat n` mentions.
Source: [[bli-overlay-mandate]] T2 step 1
Kind: L
Fidelity: n/a -/
lemma mentionedBy_BudgeterAt (DP : DeductiveProcess) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) {φ : Sentence}
    (h : MentionedBy (BudgeterAt DP Tr b Q n) φ) : MentionedBy (Tr.strat n) φ := by
  unfold BudgeterAt at h
  split at h
  · simp [MentionedBy] at h
  · rcases mentionedBy_scaleBy h with h | ⟨k, hk⟩
    · exact h
    · exact mentionedBy_of_mem_priceQueries_budgetScaleFeature DP Tr b Q n hk

/-- Component `j` of the firm on day `n` mentions only what the gated raw trader `j` mentions.
Source: [[bli-overlay-mandate]] T2 step 1
Kind: L
Fidelity: n/a -/
lemma mentionedBy_tradingFirmComponentAt (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ)
    (n j : ℕ) {φ : Sentence} (h : MentionedBy (tradingFirmComponentAt DP Q n j) φ) :
    MentionedBy ((firmRawTrader j).strat n) φ := by
  unfold tradingFirmComponentAt at h
  obtain ⟨T, hT, hTφ⟩ := mentionedBy_join h
  simp only [List.mem_append, List.mem_singleton] at hT
  rcases hT with hT | rfl
  · unfold tradingFirmBudgetComponents at hT
    simp only [List.mem_map] at hT
    obtain ⟨r, _, rfl⟩ := hT
    exact mentionedBy_BudgeterAt DP _ _ Q n (mentionedBy_scaleConst hTφ)
  · exact mentionedBy_scaleConst hTφ

/-- **Structure of the firm's mentioned set (⊆).** A sentence mentioned by the firm's day-`n`
strategy is mentioned by `(enumeratedTrader j).strat n` for some index `j ≤ n`, whatever `DP`
and `Q` are.
Source: [[bli-overlay-mandate]] T2 step 1
Kind: L
Fidelity: exact -/
lemma mentionedBy_TradingFirmAt (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ) (n : ℕ)
    {φ : Sentence} (h : MentionedBy (TradingFirmAt DP Q n) φ) :
    ∃ j ≤ n, MentionedBy ((enumeratedTrader j).strat n) φ := by
  unfold TradingFirmAt at h
  obtain ⟨T, hT, hTφ⟩ := mentionedBy_join h
  simp only [List.mem_map, List.mem_range] at hT
  obtain ⟨j, hj, rfl⟩ := hT
  have hj' : j ≤ n := Nat.lt_succ_iff.mp hj
  refine ⟨j, hj', ?_⟩
  have hraw := mentionedBy_tradingFirmComponentAt DP Q n j hTφ
  unfold firmRawTrader at hraw
  rwa [Trader.gate_strat_of_le _ hj'] at hraw

/-- **Structure of the firm's mentioned set (⊇).** Whatever `(enumeratedTrader j).strat n`
mentions, for `j ≤ n`, the firm's day-`n` strategy mentions (through the `scaleConst`ed raw copy
in component `j`).
Source: [[bli-overlay-mandate]] T2 step 1 and witness
Kind: L
Fidelity: exact -/
lemma mentionedBy_TradingFirmAt_of_enumerated (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ)
    {n j : ℕ} (hj : j ≤ n) {φ : Sentence} (h : MentionedBy ((enumeratedTrader j).strat n) φ) :
    MentionedBy (TradingFirmAt DP Q n) φ := by
  have hraw : MentionedBy (((firmRawTrader j).strat n).scaleConst
      (tradingFirmWeight j (tradingFirmCutoff n))) φ := by
    unfold firmRawTrader
    rw [Trader.gate_strat_of_le _ hj]
    exact mentionedBy_scaleConst_of _ h
  have hcomp : MentionedBy (tradingFirmComponentAt DP Q n j) φ := by
    unfold tradingFirmComponentAt
    exact mentionedBy_join_of (List.mem_append_right _ (List.mem_singleton_self _)) hraw
  unfold TradingFirmAt
  exact mentionedBy_join_of (List.mem_map.mpr ⟨j, List.mem_range.mpr (Nat.lt_succ_of_le hj), rfl⟩)
    hcomp

/-- **The firm's mentioned set is the union of its indices' mentioned sets** — independent of
`DP` and of `Q` (Known issue 5).
Source: [[bli-overlay-mandate]] T2 step 1; Known issue 5
Kind: L
Fidelity: exact -/
theorem mentionedSet_TradingFirmAt_eq (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ) (n : ℕ) :
    mentionedSet (TradingFirmAt DP Q n) =
      (Finset.range (n + 1)).biUnion fun j => mentionedSet ((enumeratedTrader j).strat n) := by
  ext φ
  simp only [Finset.mem_biUnion, Finset.mem_range, mem_mentionedSet_iff]
  constructor
  · intro h
    obtain ⟨j, hj, hφ⟩ := mentionedBy_TradingFirmAt DP Q n h
    exact ⟨j, Nat.lt_succ_of_le hj, hφ⟩
  · rintro ⟨j, hj, hφ⟩
    exact mentionedBy_TradingFirmAt_of_enumerated DP Q (Nat.lt_succ_iff.mp hj) hφ

/-! ## Step 2: size per index -/

/-- `bitsToDigits [] = []`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma bitsToDigits_nil : bitsToDigits [] = [] := by simp [bitsToDigits]

/-- The enumerated trader's day-`n` strategy is `strategyOfOutput n w` for a word `w` (the
machine's output, or `[]` on timeout) whose digit stream is no longer than the index's clock.
Source: [[bli-overlay-mandate]] T2 step 2
Kind: L
Fidelity: exact -/
lemma enumeratedTrader_strat_eq_strategyOfOutput (j n : ℕ) :
    ∃ w : List Bool, (enumeratedTrader j).strat n = strategyOfOutput n w ∧
      (bitsToDigits w).length ≤ progClock j n := by
  rcases machineTokens_steps_le j n with h | ⟨c, _, _, _, _, _, h⟩
  · refine ⟨[], ?_, by simp⟩
    rw [enumeratedTrader_strat, strategyOfOutput, h, bitsToDigits_nil]
  · refine ⟨codedOutput c, ?_, ?_⟩
    · rw [enumeratedTrader_strat, strategyOfOutput, h]
    · rw [← h]
      exact length_machineTokens_le j n

/-- **Size per index.** Every sentence mentioned by `(enumeratedTrader j).strat n` has
`tokenSize ≤ 2 ^ ((C + 6) · (progClock j n + 1))`, `C` the structured constant.
Source: [[bli-overlay-mandate]] T2 step 2
Kind: C
Fidelity: exact
Hyps: (a) — `hC` is `bli-found`'s `tokenSize_le_of_structured`, passed as the bridge lemma takes it -/
theorem tokenSize_le_of_mentionedBy_enumerated {C : ℕ}
    (hC : ∀ (ts : List ℕ) (φ : Sentence) (rest : List ℕ),
      parseStructuredPaperPrime ts = some (φ, rest) →
        tokenSize φ ≤ 2 ^ (C * (ts.length - rest.length)) + C)
    {j n : ℕ} {φ : Sentence} (h : MentionedBy ((enumeratedTrader j).strat n) φ) :
    tokenSize φ ≤ 2 ^ ((C + 6) * (progClock j n + 1)) := by
  obtain ⟨w, hw, hlen⟩ := enumeratedTrader_strat_eq_strategyOfOutput j n
  rw [hw] at h
  calc tokenSize φ ≤ bridgeBound C (bitsToDigits w).length :=
        tokenSize_le_bridgeBound_of_mentionedBy hC h
    _ ≤ bridgeBound C (progClock j n) := bridgeBound_mono C hlen
    _ ≤ 2 ^ ((C + 6) * (progClock j n + 1)) := bridgeBound_le C _

/-- **The uniform size bound for the firm** — the honest partial the mandate names if the
arithmetic stalls (it did not): every sentence the firm mentions on day `n` is bounded by the
clock of some index `j ≤ n`.
Source: [[bli-overlay-mandate]] T2 step 2
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem tokenSize_le_of_mentionedBy_firm {C : ℕ}
    (hC : ∀ (ts : List ℕ) (φ : Sentence) (rest : List ℕ),
      parseStructuredPaperPrime ts = some (φ, rest) →
        tokenSize φ ≤ 2 ^ (C * (ts.length - rest.length)) + C)
    (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ) (n : ℕ) {φ : Sentence}
    (h : MentionedBy (TradingFirmAt DP Q n) φ) :
    ∃ j ≤ n, tokenSize φ ≤ 2 ^ ((C + 6) * (progClock j n + 1)) := by
  obtain ⟨j, hj, hφ⟩ := mentionedBy_TradingFirmAt DP Q n h
  exact ⟨j, hj, tokenSize_le_of_mentionedBy_enumerated hC hφ⟩

/-! ## Step 3: the arithmetic -/

/-- `Nat.unpair`'s second component is at most `Nat.sqrt` of its input (the square-root bound
the mandate's T2 step 3 asks for; the crude `unpair_right_le` does not suffice).
Source: [[bli-overlay-mandate]] T2 step 3
Kind: L
Fidelity: n/a -/
lemma unpair_snd_le_sqrt (m : ℕ) : (Nat.unpair m).2 ≤ Nat.sqrt m := by
  have h2 := Nat.lt_succ_sqrt m
  unfold Nat.unpair
  dsimp only
  split_ifs with h
  · exact le_rfl
  · dsimp only
    generalize Nat.sqrt m = s at *
    simp only [Nat.succ_eq_add_one] at h2
    have : (s + 1) * (s + 1) = s * s + 2 * s + 1 := by ring
    omega

/-- `progCoeff j ≤ j`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma progCoeff_le (j : ℕ) : progCoeff j ≤ j :=
  le_trans (Nat.unpair_right_le _) (Nat.unpair_left_le _)

/-- `progDeg j ≤ Nat.sqrt j`.
Source: [[bli-overlay-mandate]] T2 step 3
Kind: L
Fidelity: n/a -/
lemma progDeg_le_sqrt (j : ℕ) : progDeg j ≤ Nat.sqrt j :=
  unpair_snd_le_sqrt j

/-- `4 (l+1)^2 ≤ 2^l` for `l ≥ 10`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma four_mul_sq_succ_le_two_pow (l : ℕ) (hl : 10 ≤ l) : 4 * (l + 1) ^ 2 ≤ 2 ^ l := by
  induction l, hl using Nat.le_induction with
  | base => norm_num
  | succ l hl ih =>
      calc 4 * (l + 1 + 1) ^ 2 ≤ 2 * (4 * (l + 1) ^ 2) := by nlinarith
        _ ≤ 2 * 2 ^ l := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (l + 1) := by ring

/-- **The clock estimate (T2 step 3).** For every `n ≥ 2^10 + 4C + 32` and every index `j ≤ n`,
`(C + 6)(progClock j n + 1) ≤ 2^n`. With `s = √n`, `l = log₂ n`: the coefficient is `≤ n`, the
degree `≤ s`, so `progClock j n + 1 ≤ 2 (n+1)^{s+1} ≤ 2^{1 + (l+1)(s+1)}`; and
`C + 7 + (l+1)(s+1) ≤ n` because `2(l+1) ≤ s` (from `4(l+1)^2 ≤ 2^l ≤ n`) gives
`2(l+1)(s+1) ≤ s(s+1) ≤ n + s`, and `2s ≤ n`, `4C + 32 ≤ n`.
Source: [[bli-overlay-mandate]] T2 step 3; Known issue 1
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem eventually_firm_clock_le (C : ℕ) :
    ∃ N₀, ∀ n ≥ N₀, ∀ j ≤ n, (C + 6) * (progClock j n + 1) ≤ 2 ^ n := by
  refine ⟨1024 + 4 * C + 32, fun n hn j hj => ?_⟩
  have h10 : 2 ^ 10 ≤ n := by
    calc (2 : ℕ) ^ 10 = 1024 := by norm_num
      _ ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  set s := Nat.sqrt n with hs_def
  set l := Nat.log 2 n with hl_def
  have hl10 : 10 ≤ l := Nat.le_log_of_pow_le (by norm_num) h10
  have hl_le : 2 ^ l ≤ n := Nat.pow_log_le_self 2 hn0
  have hn_lt : n < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hss : s * s ≤ n := Nat.sqrt_le n
  have h4 : 4 * (l + 1) ^ 2 ≤ n := le_trans (four_mul_sq_succ_le_two_pow l hl10) hl_le
  have h2L : 2 * (l + 1) ≤ s := by
    rw [hs_def]
    exact Nat.le_sqrt.mpr (by nlinarith)
  have hs2 : 2 ≤ s := by
    rw [hs_def]
    exact Nat.le_sqrt.mpr (by omega)
  have h2s : 2 * s ≤ n := le_trans (Nat.mul_le_mul_right s hs2) hss
  have hexp : C + 7 + (l + 1) * (s + 1) ≤ n := by
    have hprod : 2 * (l + 1) * (s + 1) ≤ s * (s + 1) := Nat.mul_le_mul_right (s + 1) h2L
    nlinarith
  have ha : progCoeff j ≤ n := le_trans (progCoeff_le j) hj
  have hk : progDeg j ≤ s := le_trans (progDeg_le_sqrt j) (Nat.sqrt_le_sqrt hj)
  have hpow1 : (n + 1) ^ progDeg j ≤ (n + 1) ^ s := Nat.pow_le_pow_right (by omega) hk
  have hclock : progClock j n + 1 ≤ 2 * (n + 1) ^ (s + 1) := by
    unfold progClock
    have h1 : progCoeff j * (n + 1) ^ progDeg j ≤ n * (n + 1) ^ s := Nat.mul_le_mul ha hpow1
    have h2 : n * (n + 1) ^ s ≤ (n + 1) ^ (s + 1) := by
      rw [pow_succ]
      exact Nat.mul_le_mul_right _ (Nat.le_succ n) |>.trans (by rw [mul_comm])
    have h3 : n + 1 ≤ (n + 1) ^ (s + 1) := by
      calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
        _ ≤ (n + 1) ^ (s + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hpow2 : (n + 1) ^ (s + 1) ≤ 2 ^ ((l + 1) * (s + 1)) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by omega) _
  have hfinal : (C + 6) * (progClock j n + 1) ≤ 2 ^ (C + 7 + (l + 1) * (s + 1)) := by
    calc (C + 6) * (progClock j n + 1) ≤ (C + 6) * (2 * (n + 1) ^ (s + 1)) :=
          Nat.mul_le_mul_left _ hclock
      _ ≤ 2 ^ (C + 6) * (2 * 2 ^ ((l + 1) * (s + 1))) :=
          Nat.mul_le_mul Nat.lt_two_pow_self.le (Nat.mul_le_mul_left 2 hpow2)
      _ = 2 ^ (C + 7 + (l + 1) * (s + 1)) := by ring
  exact le_trans hfinal (Nat.pow_le_pow_right (by norm_num) hexp)

/-! ## T2: the firm-support lemma -/

/-- **T2 (F2). The firm-support lemma.** From day `N₀ = 2^10 + 4C + 32` on (`C = 10` the
structured constant, so `N₀ = 1096`), every sentence the trading firm's day-`n` strategy mentions
— traded or read at a price leaf — is small on day `n`, for every process `DP` and every rational
table `Q` the firm is built from. The `MentionedBy` form is the headline (Known issue 2); the
`support` form is `firm_support_subset_smallSet`.
Source: [[bli-overlay-mandate]] T2; [[bli-program]] §2.1 (F2), §4 row F2
Kind: C
Fidelity: exact
Hyps: (a) — nothing assumed: the structure lemma, `bli-found`'s size bounds and the clock
estimate are all proved -/
theorem firm_mentioned_small :
    ∃ N₀, ∀ n ≥ N₀, ∀ (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ) (φ : Sentence),
      MentionedBy (TradingFirmAt DP Q n) φ → SmallOn n φ := by
  obtain ⟨C, hC⟩ := tokenSize_le_of_structured
  obtain ⟨N₀, hN₀⟩ := eventually_firm_clock_le C
  refine ⟨N₀, fun n hn DP Q φ hφ => ?_⟩
  obtain ⟨j, hj, hφj⟩ := mentionedBy_TradingFirmAt DP Q n hφ
  unfold SmallOn sizeBound
  calc tokenSize φ ≤ 2 ^ ((C + 6) * (progClock j n + 1)) :=
        tokenSize_le_of_mentionedBy_enumerated hC hφj
    _ ≤ 2 ^ (2 ^ n) := Nat.pow_le_pow_right (by norm_num) (hN₀ n hn j hj)

/-- **T2, `mentionedSet` form.** `mentionedSet (TradingFirmAt DP Q n) ⊆ smallSet n` from `N₀` on.
Source: [[bli-overlay-mandate]] T2
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem firm_mentionedSet_subset_smallSet :
    ∃ N₀, ∀ n ≥ N₀, ∀ (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ),
      mentionedSet (TradingFirmAt DP Q n) ⊆ smallSet n := by
  obtain ⟨N₀, hN₀⟩ := firm_mentioned_small
  refine ⟨N₀, fun n hn DP Q φ hφ => ?_⟩
  rw [mem_smallSet]
  exact hN₀ n hn DP Q φ (mem_mentionedSet_iff.mp hφ)

/-- **T2, the plan's wording.** `(TradingFirmAt DP Q n).support ⊆ smallSet n` from `N₀` on — the
traded sentences only; weaker than the `MentionedBy` form (Known issue 2).
Source: [[bli-overlay-mandate]] T2; [[bli-program]] §4 row F2
Kind: C
Fidelity: weaker: traded sentences only (the plan's F2 wording); the headline is the `MentionedBy` form
Hyps: (a) -/
theorem firm_support_subset_smallSet :
    ∃ N₀, ∀ n ≥ N₀, ∀ (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ),
      (TradingFirmAt DP Q n).support ⊆ smallSet n := by
  obtain ⟨N₀, hN₀⟩ := firm_mentionedSet_subset_smallSet
  exact ⟨N₀, fun n hn DP Q => (support_subset_mentionedSet _).trans (hN₀ n hn DP Q)⟩

/-! ## The witness -/

/-- **N+ for T2.** The firm's mentioned set is not empty: from the enumeration index `i` of FAF's
`buyAtomDaily` on, the firm's day-`n` strategy mentions `⌜aₙ⌝`, for every `DP` and `Q`. The day
`i` is the index `exists_enumeratedTrader_eq` returns (existential, not computed); the mentioned
sentence changes with the day.
Source: [[bli-overlay-mandate]] T2 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem firm_mentions_something :
    ∃ i, ∀ n ≥ i, ∀ (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ),
      Formula.atom n ∈ mentionedSet (TradingFirmAt DP Q n) := by
  obtain ⟨i, hi⟩ := exists_enumeratedTrader_eq buyAtomDaily efficientlyComputable_buyAtomDaily
  refine ⟨i, fun n hn DP Q => ?_⟩
  rw [mem_mentionedSet_iff]
  apply mentionedBy_TradingFirmAt_of_enumerated DP Q hn
  rw [hi]
  exact buyAtomDaily_mentions n

end Cleanroom.Bli.BliOverlay.AttemptA
