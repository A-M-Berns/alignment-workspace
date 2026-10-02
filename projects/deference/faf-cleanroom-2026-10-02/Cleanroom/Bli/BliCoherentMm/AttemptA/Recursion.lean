import Cleanroom.Bli.BliCoherentMm.AttemptA.Maker
import Cleanroom.Bli.BliCoherentMm.AttemptA.Waived

/-!
# `bli-coherent-mm` (attempt A) · Recursion: the propositionally coherent overlaid market (D5, T6, M3)

**The construction-facing file** (kept separate, plan §0.5). `bli-overlay`'s restricted-past
recursion with FAF's `MarketMaker` replaced by the **interior coherent market maker** on the
day's priced set against the restricted past, stage `DP.D n`, atom bound
`B n := (S n ∪ DP.D n).sup atomBound + 1`. The priced set is
`S n := mentionedSet (firm n) ∪ X n` for a parameter `X : ℕ → Finset Sentence`: the
**definition of record** is `X = fun _ => ∅` (price exactly the mentioned set, the maker's own
`2^B` enumeration), the **`smallSet` variant** (T2(e)) is `X = smallSet`, coherent on all of
`smallSet n` every day with the same theorems. Every statement below holds for every `X`.

Per day `n`: `pcDayStrat` is the trading firm **built from the overlaid table of the days `< n`**
(never from `liaStates`); `pcDayPast` the restricted past on `S n`; `pcDayCore` the interior
maker's state and weights **when the stage `DP.D n` has a consistent world over `B n` atoms**
(`hW`), else a fixed fallback (`emptyState`, weights `0`) — FAF's `DeductiveProcess` has no
consistency field, and in that branch no `PCWorld` is consistent with `DP.D n`
(`exists_consistent_of_pcWorld`), so every stage-relative bound is vacuous and nothing downstream
weakens. The day quote is the core quote on `S n` and the overlay `ov` elsewhere.

Headlines (all Kind C, grade (a)):
* `pcOverlay_firm_dayValue_le` — the firm's day-`n` value on the overlaid history is
  `≤ marketMakerError n` in every world consistent with `DP.D n` (T2(d) plus agreement on
  mentioned cells);
* `pcOverlay_firm_not_exploited` (T0 with `W = ∅`), **`pcOverlay_no_ec_trader_exploits`**
  (`trading_firm_dominance`);
* **`pcOverlay_coherent_mentioned`** — on every day whose stage has a consistent world, the quote
  on `S n` is the marginal of the exposed world measure `pcCoreWeights`; `pcOverlay_nonDogmatic`,
  `pcQuote_decided_true/false` (monotone on decided sentences, via `DP.mono_le`), and
  `D_PC_mentioned` in `bli-found`'s `CoherentOn` shape;
* the assembly `pcOverlay_isLogicalInductor_of_computableMarket` (Kind L; `ComputableMarket`
  **assumed**; ledger `partial: computability open`) and `PCInductor DP` (D5) inhabited by
  `pcInductor` under `hcons : ∀ n, ∃ v, v.ConsistentWith (DP.D n)` — the `noExploit` /
  `marketComputable` split is visible: `marketComputable` is not a field, and nothing here may be
  cited as a logical inductor.

Sources: [[bli-coherent-mm-mandate]] D5, T6; [[bli-program]] §2.7, §3.3, §3.8, §4 row M3, §7 item 8;
[[bli-overlay-mandate]] D3 (the recursion pattern).
-/

namespace Cleanroom.Bli.BliCoherentMm.AttemptA

open LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliOverlay

/-! ## The day record -/

/-- The empty belief state (quote `0` everywhere): the fallback core of a day whose stage has no
consistent world over the day's atoms.
Source: [[bli-coherent-mm-mandate]] T6 (the fallback)
Kind: D
Fidelity: exact -/
def emptyState : RationalBeliefState := ⟨[], List.nodup_nil, by simp⟩

/-- One day of the coherent overlaid recursion: the core state, the day's atom bound, the core's
world weights, and the overlaid quote table with its range.
Source: [[bli-coherent-mm-mandate]] D5
Kind: D
Fidelity: exact -/
structure PCDayRecord where
  /-- The day's core state (the interior maker's output, or the fallback). -/
  core : RationalBeliefState
  /-- The day's atom bound `B n`. -/
  atoms : ℕ
  /-- The core's world weights (`pcCoreWeights`). -/
  weights : FiniteWorld atoms → ℚ
  /-- The day's overlaid quote table. -/
  quote : Sentence → ℚ
  /-- Its range. -/
  range : ∀ φ, 0 ≤ quote φ ∧ quote φ ≤ 1

/-- The overlaid table of the days `< n`, read off the previous records (`0` on days `≥ n`, which
the day-`n` firm never reads).
Source: [[bli-coherent-mm-mandate]] D5; [[bli-overlay-mandate]] D3
Kind: D
Fidelity: exact -/
def pcPrevTable (n : ℕ) (prev : Fin n → PCDayRecord) : ℕ → Sentence → ℚ :=
  fun k φ => if h : k < n then (prev ⟨k, h⟩).quote φ else 0

/-- `pcPrevTable` is in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pcPrevTable_range (n : ℕ) (prev : Fin n → PCDayRecord) :
    ∀ k φ, 0 ≤ pcPrevTable n prev k φ ∧ pcPrevTable n prev k φ ≤ 1 := by
  intro k φ
  unfold pcPrevTable
  split
  · exact (prev _).range φ
  · exact ⟨le_rfl, zero_le_one⟩

/-- `pcPrevTable` on a day `< n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pcPrevTable_of_lt (n : ℕ) (prev : Fin n → PCDayRecord) {k : ℕ} (hk : k < n) (φ : Sentence) :
    pcPrevTable n prev k φ = (prev ⟨k, hk⟩).quote φ := by
  simp [pcPrevTable, hk]

section Day

variable (DP : DeductiveProcess) (X : ℕ → Finset Sentence) (n : ℕ) (prev : Fin n → PCDayRecord)

/-- The day-`n` firm strategy: the trading firm **built from the overlaid table** of the days `< n`.
Source: [[bli-coherent-mm-mandate]] T6 ("the firm built from the coherent overlaid table")
Kind: D
Fidelity: exact -/
def pcDayStrat : Strategy n := TradingFirmAt DP (pcPrevTable n prev) n

/-- The day's priced set `S n := mentionedSet (firm n) ∪ X n` (record: `X = fun _ => ∅`).
Source: [[bli-coherent-mm-mandate]] D5, T2(e)
Kind: D
Fidelity: exact -/
def pcDaySet : Finset Sentence := mentionedSet (pcDayStrat DP n prev) ∪ X n

/-- The day's atom bound `B n := (S n ∪ DP.D n).sup atomBound + 1`.
Source: [[bli-coherent-mm-mandate]] D5
Kind: D
Fidelity: exact -/
def pcDayAtoms : ℕ := (pcDaySet DP X n prev ∪ DP.D n).sup atomBound + 1

/-- Every priced and every stage sentence is within the day's atom bound.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pcDayAtoms_bound : ∀ φ ∈ pcDaySet DP X n prev ∪ DP.D n, atomBound φ ≤ pcDayAtoms DP X n prev :=
  fun _ hφ => Nat.le_succ_of_le (Finset.le_sup hφ)

/-- The restricted overlaid past fed to the maker on day `n`.
Source: [[bli-coherent-mm-mandate]] T6; [[bli-overlay-mandate]] §Attempt angles (A)
Kind: D
Fidelity: exact -/
noncomputable def pcDayPast : List RationalBeliefState :=
  BliOverlay.AttemptA.restrictedPast (pcDaySet DP X n prev) (pcPrevTable n prev)
    (pcPrevTable_range n prev) n

/-- **The day's core**: the interior coherent market maker's state and weights on the firm, the
restricted past, the stage `DP.D n`, the atom bound and the priced set, at tolerance
`marketMakerError n`, **when the stage has a consistent world over the day's atoms**; else the
fallback `(emptyState, 0)`.
Source: [[bli-coherent-mm-mandate]] D5, T6
Kind: D
Fidelity: exact -/
noncomputable def pcDayCore : RationalBeliefState × (FiniteWorld (pcDayAtoms DP X n prev) → ℚ) :=
  if hW : ∃ u : FiniteWorld (pcDayAtoms DP X n prev), (worldOf u).ConsistentWith (DP.D n) then
    (interiorCoherentMarketMaker (pcDayStrat DP n prev) (pcDayPast DP X n prev) (DP.D n)
        (pcDayAtoms DP X n prev) (pcDaySet DP X n prev) Finset.subset_union_left hW
        (marketMakerError_pos n),
      interiorWeights (pcDayStrat DP n prev) (pcDayPast DP X n prev) (DP.D n)
        (pcDayAtoms DP X n prev) (pcDaySet DP X n prev) Finset.subset_union_left hW
        (marketMakerError_pos n))
  else (emptyState, fun _ => 0)

/-- One step of the recursion: the core, its atoms and weights, and the overlaid quote (core quote
on the priced set, `ov` elsewhere).
Source: [[bli-coherent-mm-mandate]] D5
Kind: D
Fidelity: exact -/
noncomputable def pcDayStep (ov : Overlay) : PCDayRecord where
  core := (pcDayCore DP X n prev).1
  atoms := pcDayAtoms DP X n prev
  weights := (pcDayCore DP X n prev).2
  quote φ := if φ ∈ pcDaySet DP X n prev then (pcDayCore DP X n prev).1.quote φ
    else ov.val n (List.ofFn fun i => (prev i).core) (pcDayCore DP X n prev).1 φ
  range φ := by
    by_cases h : φ ∈ pcDaySet DP X n prev
    · rw [if_pos h]
      exact (pcDayCore DP X n prev).1.quote_mem_Icc φ
    · rw [if_neg h]
      exact ov.range _ _ _ _

end Day

/-! ## D5: the recursion and its readings -/

/-- **D5. The coherent overlaid recursion** (well-founded on the day).
Source: [[bli-coherent-mm-mandate]] D5; [[bli-program]] §3.3 (ii), §3.8
Kind: D
Fidelity: exact -/
noncomputable def pcRec (DP : DeductiveProcess) (ov : Overlay) (X : ℕ → Finset Sentence) : ℕ → PCDayRecord
  | n => pcDayStep DP X n (fun i : Fin n => pcRec DP ov X i) ov
termination_by n => n
decreasing_by exact i.isLt

section Record

variable (DP : DeductiveProcess) (ov : Overlay) (X : ℕ → Finset Sentence)

/-- The previous records of day `n`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def pcPrev (n : ℕ) : Fin n → PCDayRecord := fun i => pcRec DP ov X i

/-- **The core state** of day `n`.
Source: [[bli-coherent-mm-mandate]] D5 (`pcCoreState`)
Kind: D
Fidelity: exact -/
noncomputable def pcCoreState (n : ℕ) : RationalBeliefState := (pcRec DP ov X n).core

/-- **The day-`n` atom bound** `B n`.
Source: [[bli-coherent-mm-mandate]] D5 (`B n`)
Kind: D
Fidelity: exact -/
noncomputable def pcAtoms (n : ℕ) : ℕ := (pcRec DP ov X n).atoms

/-- **The core's world measure** of day `n` (exposed: `B3` needs the measure).
Source: [[bli-coherent-mm-mandate]] D5 (`pcCoreWeights`)
Kind: D
Fidelity: exact -/
noncomputable def pcCoreWeights (n : ℕ) : FiniteWorld (pcAtoms DP ov X n) → ℚ := (pcRec DP ov X n).weights

/-- **The coherent overlaid table**: the core quote on the day's priced set, the overlay elsewhere.
Source: [[bli-coherent-mm-mandate]] D5 (`pcQuote`)
Kind: D
Fidelity: exact -/
noncomputable def pcQuote : ℕ → Sentence → ℚ := fun n φ => (pcRec DP ov X n).quote φ

/-- **The coherent overlaid market**: the real history obtained by casting `pcQuote`.
Source: [[bli-coherent-mm-mandate]] D5 (`pcHistory`)
Kind: D
Fidelity: exact -/
noncomputable def pcHistory : History := fun n φ => (pcQuote DP ov X n φ : ℝ)

/-- **The firm's day-`n` strategy**: the trading firm built from the coherent overlaid table — the
strategy `tradingFirmTrader DP (pcQuote DP ov X)` plays on day `n` (`pcFirmStrat_eq`, `rfl`).
Source: [[bli-coherent-mm-mandate]] D5 (`pcFirmStrat`)
Kind: D
Fidelity: exact -/
noncomputable def pcFirmStrat (n : ℕ) : Strategy n := TradingFirmAt DP (pcQuote DP ov X) n

/-- `pcQuote` is in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pcQuote_range : ∀ k φ, 0 ≤ pcQuote DP ov X k φ ∧ pcQuote DP ov X k φ ≤ 1 :=
  fun k φ => (pcRec DP ov X k).range φ

/-- The `def:market` range clause for the coherent overlaid market (no clamp).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pcHistory_range : ∀ day φ, 0 ≤ pcHistory DP ov X day φ ∧ pcHistory DP ov X day φ ≤ 1 := by
  intro d φ
  unfold pcHistory
  exact ⟨by exact_mod_cast (pcQuote_range DP ov X d φ).1,
    by exact_mod_cast (pcQuote_range DP ov X d φ).2⟩

/-- The recursion's firm strategy is the static firm's day-`n` strategy (the wrong-market guard).
Source: [[bli-coherent-mm-mandate]] T6; [[bli-program]] §7 item 3
Kind: L
Fidelity: exact -/
lemma pcFirmStrat_eq (n : ℕ) :
    pcFirmStrat DP ov X n = (tradingFirmTrader DP (pcQuote DP ov X)).strat n := rfl

/-- The recursion's equation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pcRec_unfold (n : ℕ) : pcRec DP ov X n = pcDayStep DP X n (pcPrev DP ov X n) ov := by
  rw [pcRec]
  rfl

/-- The previous-records table is the overlaid table on days `< n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pcPrevTable_pcPrev (n : ℕ) {k : ℕ} (hk : k < n) (φ : Sentence) :
    pcPrevTable n (pcPrev DP ov X n) k φ = pcQuote DP ov X k φ := by
  rw [pcPrevTable_of_lt n _ hk]
  rfl

/-- **The recursion's day-`n` strategy is `pcFirmStrat`**: the firm reads only days `< n`
(`TradingFirmAt_eq_of_eq_prefix`).
Source: [[bli-coherent-mm-mandate]] T6
Kind: L
Fidelity: exact -/
lemma pcDayStrat_eq_firmStrat (n : ℕ) : pcDayStrat DP n (pcPrev DP ov X n) = pcFirmStrat DP ov X n := by
  unfold pcDayStrat pcFirmStrat
  apply TradingFirmAt_eq_of_eq_prefix
  intro k hk φ
  exact pcPrevTable_pcPrev DP ov X n hk φ

/-- The day-`n` priced set, in terms of the record's firm: `mentionedSet (pcFirmStrat n) ∪ X n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pcDaySet_eq (n : ℕ) : pcDaySet DP X n (pcPrev DP ov X n) = mentionedSet (pcFirmStrat DP ov X n) ∪ X n := by
  unfold pcDaySet
  rw [pcDayStrat_eq_firmStrat]

/-- **The day-`n` priced set** of the record: `mentionedSet (pcFirmStrat n) ∪ X n`.
Source: [[bli-coherent-mm-mandate]] D5
Kind: D
Fidelity: exact -/
noncomputable def pcSet (n : ℕ) : Finset Sentence := mentionedSet (pcFirmStrat DP ov X n) ∪ X n

/-- The day's atoms are the recorded atom bound.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pcAtoms_eq (n : ℕ) : pcAtoms DP ov X n = pcDayAtoms DP X n (pcPrev DP ov X n) := by
  unfold pcAtoms
  rw [pcRec_unfold]
  rfl

/-- **`B n` in the record's terms**: `(pcSet n ∪ DP.D n).sup atomBound + 1`.
Source: [[bli-coherent-mm-mandate]] D5
Kind: L
Fidelity: exact -/
lemma pcAtoms_eq_sup (n : ℕ) : pcAtoms DP ov X n = (pcSet DP ov X n ∪ DP.D n).sup atomBound + 1 := by
  rw [pcAtoms_eq]
  unfold pcDayAtoms pcSet
  rw [pcDaySet_eq]

/-- Every priced and every stage sentence of day `n` is within `B n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pcAtoms_bound (n : ℕ) : ∀ φ ∈ pcSet DP ov X n ∪ DP.D n, atomBound φ ≤ pcAtoms DP ov X n := by
  intro φ hφ
  rw [pcAtoms_eq_sup]
  exact Nat.le_succ_of_le (Finset.le_sup hφ)

/-- The quote on the priced set is the core quote.
Source: [[bli-coherent-mm-mandate]] D5
Kind: L
Fidelity: exact -/
lemma pcQuote_of_mem (n : ℕ) {φ : Sentence} (hφ : φ ∈ pcSet DP ov X n) :
    pcQuote DP ov X n φ = (pcCoreState DP ov X n).quote φ := by
  unfold pcQuote pcCoreState
  rw [pcRec_unfold]
  have h : φ ∈ pcDaySet DP X n (pcPrev DP ov X n) := by rwa [pcDaySet_eq]
  simp only [pcDayStep, if_pos h]

/-- Off the priced set the quote is the overlay.
Source: [[bli-coherent-mm-mandate]] D5
Kind: L
Fidelity: exact -/
lemma pcQuote_of_not_mem (n : ℕ) {φ : Sentence} (hφ : φ ∉ pcSet DP ov X n) :
    pcQuote DP ov X n φ =
      ov.val n (List.ofFn fun i : Fin n => pcCoreState DP ov X i) (pcCoreState DP ov X n) φ := by
  unfold pcQuote pcCoreState
  rw [pcRec_unfold]
  have h : φ ∉ pcDaySet DP X n (pcPrev DP ov X n) := by rwa [pcDaySet_eq]
  simp only [pcDayStep, if_neg h]
  rfl

/-- The restricted past of day `n`, in the record's terms.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def pcPast (n : ℕ) : List RationalBeliefState :=
  pcDayPast DP X n (pcPrev DP ov X n)

/-- On days `< n` and priced sentences the restricted past reads the overlaid table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma rationalHistory_pcPast (n : ℕ) {k : ℕ} (hk : k < n) {φ : Sentence} (hφ : φ ∈ pcSet DP ov X n) :
    rationalHistory (pcPast DP ov X n) k φ = pcQuote DP ov X k φ := by
  unfold pcPast pcDayPast
  have h : φ ∈ pcDaySet DP X n (pcPrev DP ov X n) := by rwa [pcDaySet_eq]
  rw [BliOverlay.AttemptA.rationalHistory_restrictedPast hk h, pcPrevTable_pcPrev DP ov X n hk]

/-- **The core of a day whose stage has a consistent world**: its weights are accepted with full
support (D3, interior clause) against the day's firm, restricted past, stage, atoms and priced
set at `marketMakerError n`, and its quote on the priced set is their marginal.
Source: [[bli-coherent-mm-mandate]] T6 (`pcCoreState_quote_eq_pi`)
Kind: L
Fidelity: exact -/
theorem pcCore_spec (n : ℕ)
    (hW : ∃ u : FiniteWorld (pcAtoms DP ov X n), (worldOf u).ConsistentWith (DP.D n)) :
    CoherentAcceptsFull (pcDayStrat DP n (pcPrev DP ov X n)) (pcPast DP ov X n) (DP.D n)
        (pcAtoms DP ov X n) (pcDaySet DP X n (pcPrev DP ov X n)) (marketMakerError n)
        (pcCoreWeights DP ov X n) ∧
      ∀ φ ∈ pcDaySet DP X n (pcPrev DP ov X n),
        (pcCoreState DP ov X n).quote φ = marginal (pcCoreWeights DP ov X n) φ := by
  have hW' : ∃ u : FiniteWorld (pcDayAtoms DP X n (pcPrev DP ov X n)),
      (worldOf u).ConsistentWith (DP.D n) := by
    rw [← pcAtoms_eq]
    exact hW
  have key : ∀ R : PCDayRecord, R = pcDayStep DP X n (pcPrev DP ov X n) ov →
      CoherentAcceptsFull (pcDayStrat DP n (pcPrev DP ov X n)) (pcPast DP ov X n) (DP.D n)
          R.atoms (pcDaySet DP X n (pcPrev DP ov X n)) (marketMakerError n) R.weights ∧
        ∀ φ ∈ pcDaySet DP X n (pcPrev DP ov X n), R.core.quote φ = marginal R.weights φ := by
    rintro R rfl
    unfold pcPast
    simp only [pcDayStep]
    unfold pcDayCore
    rw [dif_pos hW']
    exact ⟨interiorWeights_spec _ _ _ _ _ Finset.subset_union_left hW' (marketMakerError_pos n),
      fun φ hφ => interior_quote_eq_pi _ _ _ _ _ Finset.subset_union_left hW'
        (marketMakerError_pos n) hφ⟩
  exact key _ (pcRec_unfold DP ov X n)

/-- The core state of a day whose stage has a consistent world **is** the interior coherent
market maker on the day's firm against the restricted past (the recursion-to-record tie).
Source: [[bli-coherent-mm-mandate]] T6 (`pcCoreState`)
Kind: L
Fidelity: exact -/
theorem pcCoreState_eq_interior (n : ℕ)
    (hW : ∃ u : FiniteWorld (pcDayAtoms DP X n (pcPrev DP ov X n)), (worldOf u).ConsistentWith (DP.D n)) :
    pcCoreState DP ov X n =
      interiorCoherentMarketMaker (pcDayStrat DP n (pcPrev DP ov X n)) (pcPast DP ov X n) (DP.D n)
        (pcDayAtoms DP X n (pcPrev DP ov X n)) (pcDaySet DP X n (pcPrev DP ov X n))
        Finset.subset_union_left hW (marketMakerError_pos n) := by
  unfold pcCoreState pcPast
  rw [pcRec_unfold]
  simp only [pcDayStep]
  unfold pcDayCore
  rw [dif_pos hW]

/-- The stage of a day with a consistent `PCWorld` has a consistent finite world over `B n` atoms.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pc_hW_of_pcWorld (n : ℕ) (hcons : ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ u : FiniteWorld (pcAtoms DP ov X n), (worldOf u).ConsistentWith (DP.D n) :=
  exists_consistent_of_pcWorld (fun φ hφ => pcAtoms_bound DP ov X n φ (Finset.mem_union_right _ hφ))
    hcons

/-! ## T6: no efficiently computable trader exploits the coherent overlaid market -/

/-- **T6, the day bound.** The firm's day-`n` strategy — built from and evaluated on the coherent
overlaid history — has value at most `marketMakerError n` in every world consistent with
`DP.D n`: the core weights are coherently accepted against the restricted past (when the stage has
a consistent world; else vacuous), and the candidate table agrees with the overlaid history on
every mentioned cell (days `< n` by the restriction, day `n` because the quote is the core quote
on the priced set), so T2(d) applies. Scope: over `DP.D n`-consistent worlds.
Source: [[bli-coherent-mm-mandate]] T6 (`pcOverlay_firm_dayValue_le`); [[bli-program]] §3.3 (i)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem pcOverlay_firm_dayValue_le (n : ℕ) :
    ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      (pcFirmStrat DP ov X n).value (pcHistory DP ov X) v.payout ≤ (marketMakerError n : ℝ) := by
  intro v hv
  have hW := pc_hW_of_pcWorld DP ov X n ⟨v, hv⟩
  obtain ⟨hacc, hquote⟩ := pcCore_spec DP ov X n hW
  rw [← pcDayStrat_eq_firmStrat]
  refine dayValue_le_of_coherentAccepts (pcDayStrat DP n (pcPrev DP ov X n)) (pcPast DP ov X n)
    (DP.D n) (pcAtoms DP ov X n) (pcDaySet DP X n (pcPrev DP ov X n)) ?_ hacc.2 (pcHistory DP ov X)
    ?_ v hv
  · intro φ hφ
    apply pcAtoms_bound DP ov X n
    rcases Finset.mem_union.mp hφ with h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (support_subset_mentionedSet _ (by rwa [pcDayStrat_eq_firmStrat] at h)))
    · exact Finset.mem_union_right _ h
  · intro φ hφ k hk
    have hφS : φ ∈ pcDaySet DP X n (pcPrev DP ov X n) :=
      Finset.mem_union_left _ (mem_mentionedSet_iff.mpr hφ)
    have hφS' : φ ∈ pcSet DP ov X n := by rwa [pcDaySet_eq] at hφS
    rcases Nat.lt_or_eq_of_le hk with hk | rfl
    · rw [candidateTable_of_ne _ hk.ne, rationalHistory_pcPast DP ov X n hk hφS']
      rfl
    · rw [candidateTable_self_of_mem _ _ _ hφS, ← hquote φ hφS]
      unfold pcHistory
      rw [pcQuote_of_mem DP ov X k hφS']

/-- **T6. The firm does not exploit the coherent overlaid market**: T0 with `W = ∅`.
Source: [[bli-coherent-mm-mandate]] T6 (`pcOverlay_firm_not_exploited`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem pcOverlay_firm_not_exploited :
    ¬ (tradingFirmTrader DP (pcQuote DP ov X)).Exploits (pcHistory DP ov X) DP :=
  firm_not_exploits_of_coherentAccepted_off_finite DP (pcQuote DP ov X) (pcQuote_range DP ov X) ∅
    (fun n _ v hv => pcOverlay_firm_dayValue_le DP ov X n v hv)

/-- **T6 (M3, headline, load-bearing). No efficiently computable trader exploits the coherent
overlaid market**, for every process `DP`, overlay `ov` and priced-set parameter `X`: an exploiting
e.c. trader would make the static firm on the coherent table exploit it (FAF's
`trading_firm_dominance`), and the firm does not (`pcOverlay_firm_not_exploited`). Scope clause:
this is the `noExploit` half of the criterion; `ComputableMarket (pcHistory DP ov X)` is **not**
established here (the assembly lemma assumes it).
Source: [[bli-coherent-mm-mandate]] T6 (`pcOverlay_no_ec_trader_exploits`); [[bli-program]] §4 row M3
Kind: C
Fidelity: exact
Hyps: (a) — `trading_firm_dominance` is FAF's theorem, applied; `ov.range` is a field -/
theorem pcOverlay_no_ec_trader_exploits (Tr : Trader) (hTr : EfficientlyComputable Tr) :
    ¬ Tr.Exploits (pcHistory DP ov X) DP :=
  no_ec_trader_exploits_of_firm_coherentAccepted_off_finite DP (pcQuote DP ov X)
    (pcQuote_range DP ov X) ∅ (fun n _ v hv => pcOverlay_firm_dayValue_le DP ov X n v hv) Tr hTr

/-! ## T6: coherence on the priced set, every day -/

/-- **T6 (M3, headline). The coherent overlaid market is exactly coherent on its priced set every
day**: on a day `n` whose stage has a consistent world, `pcCoreWeights n` is a world measure over
`DP.D n` on `B n` atoms and the day-`n` quote of every `φ ∈ pcSet n = mentionedSet (pcFirmStrat n) ∪ X n`
is its marginal `π (pcCoreWeights n) φ`. (On a day with no consistent world nothing is coherent
in the world-marginal sense and nothing is claimed; FAF's `DeductiveProcess` does not exclude such
days — attempt findings.)
Source: [[bli-coherent-mm-mandate]] T6 (`pcOverlay_coherent_mentioned`); [[bli-program]] §4 row M3
Kind: C
Fidelity: variant: coherence as agreement with a world marginal on the priced set (as
`coherentMarketMaker_coherent`), conditional on the stage having a consistent world
Hyps: (a) `hcons` (the stage has a consistent `PCWorld`; from `paperDP_hworld` at the witness) -/
theorem pcOverlay_coherent_mentioned (n : ℕ) (hcons : ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    IsWorldMeasure (pcCoreWeights DP ov X n) (DP.D n) ∧
      ∀ φ ∈ pcSet DP ov X n, pcQuote DP ov X n φ = marginal (pcCoreWeights DP ov X n) φ := by
  obtain ⟨hacc, hquote⟩ := pcCore_spec DP ov X n (pc_hW_of_pcWorld DP ov X n hcons)
  refine ⟨hacc.2.1, fun φ hφ => ?_⟩
  rw [pcQuote_of_mem DP ov X n hφ]
  exact hquote φ (by rwa [pcDaySet_eq])

/-- The coherence headline in the `CoherentQuoteOn` form.
Source: [[bli-coherent-mm-mandate]] T6
Kind: L
Fidelity: as `pcOverlay_coherent_mentioned` -/
theorem pcOverlay_coherentQuoteOn (n : ℕ) (hcons : ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    CoherentQuoteOn (pcQuote DP ov X n) (pcSet DP ov X n) (DP.D n) (pcAtoms DP ov X n) :=
  ⟨pcCoreWeights DP ov X n, (pcOverlay_coherent_mentioned DP ov X n hcons).1,
    (pcOverlay_coherent_mentioned DP ov X n hcons).2⟩

/-- **`pcCoreState_quote_eq_pi`**: the core state quotes the exposed measure's marginal on the
priced set (on a day with a consistent world).
Source: [[bli-coherent-mm-mandate]] T6 (`pcCoreState_quote_eq_pi`)
Kind: L
Fidelity: exact -/
theorem pcCoreState_quote_eq_pi (n : ℕ) (hcons : ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {φ : Sentence} (hφ : φ ∈ pcSet DP ov X n) :
    (pcCoreState DP ov X n).quote φ = marginal (pcCoreWeights DP ov X n) φ := by
  rw [← pcQuote_of_mem DP ov X n hφ]
  exact (pcOverlay_coherent_mentioned DP ov X n hcons).2 φ hφ

/-- The core's measure has full support on the stage's consistent worlds (on a day with a
consistent world).
Source: [[bli-coherent-mm-mandate]] T6 (`pcOverlay_nonDogmatic`)
Kind: L
Fidelity: exact -/
theorem pcCoreWeights_fullSupport (n : ℕ) (hcons : ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ u ∈ WD (DP.D n) (pcAtoms DP ov X n), 0 < pcCoreWeights DP ov X n u :=
  (pcCore_spec DP ov X n (pc_hW_of_pcWorld DP ov X n hcons)).1.1

/-- **T6. Non-dogmatism**: a priced sentence held by some world consistent with `DP.D n` and
refuted by another is quoted strictly inside `(0,1)` on day `n`.
Source: [[bli-coherent-mm-mandate]] T6 (`pcOverlay_nonDogmatic`); T3
Kind: C
Fidelity: exact
Hyps: (a) `hcons` is implied by `h1` -/
theorem pcOverlay_nonDogmatic (n : ℕ) {φ : Sentence} (hφ : φ ∈ pcSet DP ov X n)
    (h1 : ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds φ)
    (h2 : ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ ¬ v.Holds φ) :
    0 < pcQuote DP ov X n φ ∧ pcQuote DP ov X n φ < 1 := by
  obtain ⟨v₁, hv₁, h₁⟩ := h1
  obtain ⟨v₂, hv₂, h₂⟩ := h2
  have hcons : ∃ v : PCWorld, v.ConsistentWith (DP.D n) := ⟨v₁, hv₁⟩
  rw [(pcOverlay_coherent_mentioned DP ov X n hcons).2 φ hφ]
  have hD : ∀ ψ ∈ DP.D n, atomBound ψ ≤ pcAtoms DP ov X n :=
    fun ψ hψ => pcAtoms_bound DP ov X n ψ (Finset.mem_union_right _ hψ)
  have hφB : atomBound φ ≤ pcAtoms DP ov X n := pcAtoms_bound DP ov X n φ (Finset.mem_union_left _ hφ)
  apply nonDogmatic_of_fullSupport (pcOverlay_coherent_mentioned DP ov X n hcons).1
    (pcCoreWeights_fullSupport DP ov X n hcons)
  · exact ⟨_, restrict_mem_WD hD hv₁, (holds_worldOf_restrict v₁ hφB).mpr h₁⟩
  · exact ⟨_, restrict_mem_WD hD hv₂, fun h => h₂ ((holds_worldOf_restrict v₂ hφB).mp h)⟩

/-- **T6. Monotone on decided sentences (true)**: a sentence decided true by `DP.D m` is, on
every later day `n ≥ m` on which it is priced, quoted `1` (`DP.mono_le` plus T2(c)).
Source: [[bli-coherent-mm-mandate]] T6 (`pcQuote_decided_monotone`)
Kind: C
Fidelity: exact
Hyps: (a) `hcons` (day `n` has a consistent world) -/
theorem pcQuote_decided_true {m n : ℕ} (hmn : m ≤ n) (hcons : ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {φ : Sentence} (hφ : φ ∈ pcSet DP ov X n)
    (hdec : ∀ v : PCWorld, v.ConsistentWith (DP.D m) → v.Holds φ) :
    pcQuote DP ov X n φ = 1 := by
  rw [(pcOverlay_coherent_mentioned DP ov X n hcons).2 φ hφ]
  exact marginal_of_decided_true (pcOverlay_coherent_mentioned DP ov X n hcons).1
    fun v hv => hdec v fun ψ hψ => hv ψ (DP.mono_le hmn hψ)

/-- **T6. Monotone on decided sentences (false)**: a sentence decided false by `DP.D m` is, on
every later day `n ≥ m` on which it is priced, quoted `0`.
Source: [[bli-coherent-mm-mandate]] T6 (`pcQuote_decided_monotone`)
Kind: C
Fidelity: exact
Hyps: (a) `hcons` -/
theorem pcQuote_decided_false {m n : ℕ} (hmn : m ≤ n) (hcons : ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {φ : Sentence} (hφ : φ ∈ pcSet DP ov X n)
    (hdec : ∀ v : PCWorld, v.ConsistentWith (DP.D m) → ¬ v.Holds φ) :
    pcQuote DP ov X n φ = 0 := by
  rw [(pcOverlay_coherent_mentioned DP ov X n hcons).2 φ hφ]
  exact marginal_of_decided_false (pcOverlay_coherent_mentioned DP ov X n hcons).1
    fun v hv => hdec v fun ψ hψ => hv ψ (DP.mono_le hmn hψ)

/-! ## `D_PC` on the mentioned set, in `bli-found`'s shape -/

/-- **`D_PC_mentioned`**: a rational table is, on every day, the marginal on the day's firm's
mentioned set of a finite mixture of `PCWorld`s consistent with the stage — `bli-found`'s
`CoherentOn` witness shape (`Fin k`-indexed worlds and real weights), restricted from "all
sentences within an atom set" to the mentioned sentences. `D_PC` of record (over all of
`smallSet n`'s sentences, in that shape) is **not** what this package's table satisfies: the
gap is the quantifier over sentences (ledger).
Source: [[bli-coherent-mm-mandate]] T6 (`D_PC_mentioned`); bli-found `D_PC`, `CoherentOn`
Kind: D
Fidelity: variant: mentioned set in place of `smallSet n`'s atom closure -/
def D_PC_mentioned (Q : ℕ → Sentence → ℚ) (DP : DeductiveProcess) : Prop :=
  ∀ n, ∃ (k : ℕ) (W : Fin k → PCWorld) (w : Fin k → ℝ),
    (∀ i, (W i).ConsistentWith (DP.D n)) ∧ (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
    ∀ φ ∈ mentionedSet (TradingFirmAt DP Q n), (Q n φ : ℝ) = ∑ i, w i * (W i).payout φ

/-- A world measure over `D` on `B` atoms is a finite mixture of `D`-consistent `PCWorld`s
(`Fin (2^B)`-indexed through `Fintype.equivFin`), with the marginal as its mixture payout.
Source: none: infrastructure (the bridge to `bli-found`'s shape)
Kind: L
Fidelity: n/a -/
lemma exists_mixture_of_isWorldMeasure {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) :
    ∃ (k : ℕ) (W : Fin k → PCWorld) (w' : Fin k → ℝ),
      (∀ i, (W i).ConsistentWith D) ∧ (∀ i, 0 ≤ w' i) ∧ ∑ i, w' i = 1 ∧
      ∀ φ, (marginal w φ : ℝ) = ∑ i, w' i * (W i).payout φ := by
  classical
  let e := Fintype.equivFin (FiniteWorld B)
  -- worlds with weight zero are replaced by a consistent one, so every listed world is consistent
  obtain ⟨u₀, hu₀⟩ : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D := by
    by_contra hcon
    simp only [not_exists] at hcon
    have h0 : ∑ u, w u = 0 := Finset.sum_eq_zero fun u _ => by
      by_contra h
      exact hcon u (hw.2.2 u h)
    rw [hw.2.1] at h0
    exact one_ne_zero h0
  let W : Fin (Fintype.card (FiniteWorld B)) → PCWorld := fun i =>
    if w (e.symm i) = 0 then worldOf u₀ else worldOf (e.symm i)
  let w' : Fin (Fintype.card (FiniteWorld B)) → ℝ := fun i => (w (e.symm i) : ℝ)
  refine ⟨_, W, w', fun i => ?_, fun i => ?_, ?_, fun φ => ?_⟩
  · simp only [W]
    split_ifs with h
    · exact hu₀
    · exact hw.2.2 _ h
  · show (0 : ℝ) ≤ (w (e.symm i) : ℝ)
    exact_mod_cast hw.1 _
  · show ∑ i, (w (e.symm i) : ℝ) = 1
    rw [Equiv.sum_comp e.symm (fun u => (w u : ℝ))]
    exact_mod_cast hw.2.1
  · unfold marginal
    push_cast
    calc ∑ u, (w u : ℝ) * (u.payoutRat φ : ℝ)
        = ∑ i, (w (e.symm i) : ℝ) * ((e.symm i).payoutRat φ : ℝ) :=
          (Equiv.sum_comp e.symm (fun u => (w u : ℝ) * (u.payoutRat φ : ℝ))).symm
      _ = ∑ i, w' i * (W i).payout φ := by
          apply Finset.sum_congr rfl
          intro i _
          simp only [W, w']
          split_ifs with h
          · rw [h]
            simp
          · rw [← payoutReal_eq_payout]
            rfl

/-- **T6. The coherent overlaid table satisfies `D_PC_mentioned`** whenever every stage has a
consistent world: every day's quote on the firm's mentioned set is a finite mixture of
`DP.D n`-consistent `PCWorld`s (`bli-found`'s shape).
Source: [[bli-coherent-mm-mandate]] T6 (`D_PC_mentioned`)
Kind: C
Fidelity: variant: mentioned set (see `D_PC_mentioned`)
Hyps: (a) `hcons` -/
theorem pcOverlay_D_PC_mentioned (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    D_PC_mentioned (pcQuote DP ov X) DP := by
  intro n
  obtain ⟨hw, hquote⟩ := pcOverlay_coherent_mentioned DP ov X n (hcons n)
  obtain ⟨k, W, w', hW, hw0, hw1, hmix⟩ := exists_mixture_of_isWorldMeasure hw
  refine ⟨k, W, w', hW, hw0, hw1, fun φ hφ => ?_⟩
  rw [hquote φ (Finset.mem_union_left _ hφ)]
  exact hmix φ

/-! ## The assembly and `PCInductor` -/

/-- **Assembly lemma (Kind L).** The coherent overlaid market is a logical inductor **if** it is a
computable market — `ComputableMarket` is **assumed**, as in FAF's
`lia_isLogicalInductor_of_computableMarket` and `bli-overlay`'s assembly; nothing in this package
establishes it. Ledger row: `partial: computability open`.
Source: [[bli-coherent-mm-mandate]] T6 (assembly); [[bli-program]] §7 item 8
Kind: L
Fidelity: weaker: `ComputableMarket (pcHistory DP ov X)` is a hypothesis, not proved
Hyps: (b) `hmarket : ComputableMarket (pcHistory DP ov X)` — assumed (open); (a) `hDP` is the
process's computability, the criterion's own hypothesis -/
theorem pcOverlay_isLogicalInductor_of_computableMarket (hDP : ComputableDeductiveProcess DP)
    (hmarket : ComputableMarket (pcHistory DP ov X)) : IsLogicalInductor (pcHistory DP ov X) DP :=
  ⟨hmarket, hDP, pcOverlay_no_ec_trader_exploits DP ov X⟩

end Record

/-- **D5. A propositionally coherent inductor** (modulo computability) over `DP`: an exactly
rational `[0,1]` table that is, every day, the marginal on its own firm's mentioned set of a world
measure over the day's stage (within an atom bound), and that no efficiently computable trader
exploits. `marketComputable` is **not** a field: it is the separate open predicate
`ComputableMarket` (program §7 item 8); an inhabitant of this structure is **not** a logical
inductor.
Source: [[bli-coherent-mm-mandate]] D5; [[bli-program]] §2.7
Kind: D
Fidelity: variant: `coh` as agreement with a world marginal on the mentioned set; no `li` field
(the program's `li : IsLogicalInductor` is replaced by `noExploit`, the computability being open) -/
structure PCInductor (DP : DeductiveProcess) where
  /-- The exact rational table. -/
  Q : ℕ → Sentence → ℚ
  /-- The `def:market` range clause. -/
  range : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1
  /-- Coherence on the firm's mentioned set, every day. -/
  coh : ∀ n, ∃ (B : ℕ) (w : FiniteWorld B → ℚ), IsWorldMeasure w (DP.D n) ∧
    (∀ φ ∈ mentionedSet (TradingFirmAt DP Q n) ∪ DP.D n, atomBound φ ≤ B) ∧
    ∀ φ ∈ mentionedSet (TradingFirmAt DP Q n), Q n φ = marginal w φ
  /-- No efficiently computable trader exploits the table's market. -/
  noExploit : ∀ Tr : Trader, EfficientlyComputable Tr → ¬ Tr.Exploits (fun n φ => (Q n φ : ℝ)) DP

/-- **T6. `PCInductor DP` is inhabited** by the coherent overlaid recursion, for every overlay and
priced-set parameter, whenever every stage of `DP` has a consistent world. Ledger: "inhabited;
`ComputableMarket` open".
Source: [[bli-coherent-mm-mandate]] T6 (`PCInductor`); [[bli-program]] §4 row M3
Kind: C
Fidelity: variant: as `PCInductor`
Hyps: (a) `hcons` (every stage has a consistent `PCWorld`; `paperDP_hworld` at the witness) -/
noncomputable def pcInductor (DP : DeductiveProcess) (ov : Overlay) (X : ℕ → Finset Sentence)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) : PCInductor DP where
  Q := pcQuote DP ov X
  range := pcQuote_range DP ov X
  coh n := ⟨pcAtoms DP ov X n, pcCoreWeights DP ov X n,
    (pcOverlay_coherent_mentioned DP ov X n (hcons n)).1,
    fun φ hφ => pcAtoms_bound DP ov X n φ (by
      rcases Finset.mem_union.mp hφ with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
      · exact Finset.mem_union_right _ h),
    fun φ hφ => (pcOverlay_coherent_mentioned DP ov X n (hcons n)).2 φ (Finset.mem_union_left _ hφ)⟩
  noExploit := pcOverlay_no_ec_trader_exploits DP ov X

/-- The inhabitant's table is the recursion's.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pcInductor_Q (DP : DeductiveProcess) (ov : Overlay) (X : ℕ → Finset Sentence)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (pcInductor DP ov X hcons).Q = pcQuote DP ov X := rfl

/-- **The `smallSet` variant (T2(e), `pcOverlaySmall`)**: with `X = smallSet` the recursion is
coherent on all of `smallSet n ∪ mentionedSet n` every day (same theorems, instantiated).
Source: [[bli-coherent-mm-mandate]] T6 (`pcOverlaySmall`), T2(e)
Kind: C
Fidelity: exact (instance)
Hyps: (a) `hcons` -/
theorem pcOverlaySmall_coherent (DP : DeductiveProcess) (ov : Overlay) (n : ℕ)
    (hcons : ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    IsWorldMeasure (pcCoreWeights DP ov smallSet n) (DP.D n) ∧
      ∀ φ ∈ smallSet n, pcQuote DP ov smallSet n φ = marginal (pcCoreWeights DP ov smallSet n) φ :=
  ⟨(pcOverlay_coherent_mentioned DP ov smallSet n hcons).1, fun φ hφ =>
    (pcOverlay_coherent_mentioned DP ov smallSet n hcons).2 φ (Finset.mem_union_right _ hφ)⟩

end Cleanroom.Bli.BliCoherentMm.AttemptA
