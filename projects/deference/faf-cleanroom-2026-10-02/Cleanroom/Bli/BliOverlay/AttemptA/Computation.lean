import Cleanroom.Bli.BliOverlay.AttemptA.Recursion
import LogicalInduction.Construction.LIAComputation

/-!
# `bli-overlay` (attempt A) · Computation: the bounded evaluator for the overlaid recursion (T6)

**T6 (stretch, L6(b)) — what is and is not done here.** This file mirrors FAF's
`Construction/LIAComputation.lean` for the overlaid recursion of `Recursion.lean`:

* **Finite day records** `OvRecord` (the core state and the day's mentioned set — the overlaid
  day table is a function on all sentences and cannot be stored; it is recomputed from the
  records by `recTable`, which is where the overlay `ov` is read: on day `k` at an unmentioned
  sentence, `ov.val k (cores < k) core_k φ`, a function of finite data).
* **The bounded evaluator** `overlayPrefixAtFuel D ov fuel n` over an explicit stage table `D`:
  day `n` builds `TradingFirmAtFromStages D (recTable ov past) n`, the restricted past
  `restrictedPastL` (the sorted `supportSentenceList` order, computable), and runs
  `marketMakerSearchUpTo` under the common fuel. With the three-lemma shape of FAF:
  `_mono_success`, **`_sound`** (a success is the semantic prefix `overlayRecPrefix DP ov n` of
  `coreState`/`firmStrat`, when `D` agrees with `DP.D` below `n`) and `exists_`.
* **The process composite** `overlayPrefixAtFuelP process ov` (decode the stages with
  `processStagePrefixAtFuel`, then run), the **encoded quote evaluators**
  `overlayEncodedQuoteAtFuel` / `overlayEncodedQuoteNatAtFuel` with soundness against
  `overlayEncodedQuote DP ov day code` (the quote of a sentence *code*; malformed codes quote
  `0`) and eventual success.
* **The compiler boundary** `OverlayBoundedEvaluatorCompiler process ov`: the one structure
  asserting that the bounded evaluator is a computable two-argument natural function. From it,
  exactly as FAF does: `quote_computable`, `exists_quote_code`, `toComputableMarket :
  ComputableMarket (overlayHistory DP ov)` and `overlay_isLogicalInductor_of_compiler`.

**Not done: the boundary is not instantiated.** FAF instantiates its own boundary in
`LIACompiler.lean` (4041 lines); the same work for this evaluator — a primitive-recursive
compilation of the day step, which is where `ov`'s computability would have to enter (as a
computable function of the encoded finite records) — was not attempted. So nothing here proves
`ComputableMarket (overlayHistory DP ov)`; the assembly lemma's ledger row stays
`partial: computability open`, and the boundary's instantiation is the open item. What this file
establishes is that the *only* missing piece is the compilation certificate: the evaluator, its
soundness and the reduction of `ComputableMarket` to the certificate are proved.

Sources: [[bli-overlay-mandate]] T6; [[bli-program]] §3.3 (b), §7 item 8; [[bli-found-liacomputation]] §4.
-/

namespace Cleanroom.Bli.BliOverlay.AttemptA

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## The restricted past in a computable order -/

/-- `supportSentenceList S` has no duplicates.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma supportSentenceList_nodup (S : Finset Sentence) : (supportSentenceList S).Nodup := by
  simp [supportSentenceList]

/-- Membership in `supportSentenceList S`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_supportSentenceList {S : Finset Sentence} {φ : Sentence} :
    φ ∈ supportSentenceList S ↔ φ ∈ S := by
  simp [supportSentenceList]

/-- The restricted state over an explicit duplicate-free list of sentences (computable, unlike
`restrictState`, which uses `Finset.toList`).
Source: [[bli-overlay-mandate]] T6
Kind: D
Fidelity: exact -/
def restrictStateL (l : List Sentence) (hl : l.Nodup) (q : Sentence → ℚ)
    (hq : ∀ φ, 0 ≤ q φ ∧ q φ ≤ 1) : RationalBeliefState where
  entries := l.map fun φ => (φ, q φ)
  keys_nodup := by
    rw [List.map_map]
    simpa [Function.comp_def] using hl
  bounded := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨φ, _, rfl⟩ := hp
    exact hq φ

/-- On `l`, `restrictStateL` quotes the table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma restrictStateL_quote_of_mem {l : List Sentence} {hl : l.Nodup} {q : Sentence → ℚ}
    {hq : ∀ φ, 0 ≤ q φ ∧ q φ ≤ 1} {φ : Sentence} (hφ : φ ∈ l) :
    (restrictStateL l hl q hq).quote φ = q φ := by
  unfold restrictStateL RationalBeliefState.quote
  exact quoteFromEntries_map_eq hl q hφ

/-- The restricted past in the computable `supportSentenceList` order.
Source: [[bli-overlay-mandate]] T6
Kind: D
Fidelity: exact -/
def restrictedPastL (S : Finset Sentence) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ k φ, 0 ≤ Q k φ ∧ Q k φ ≤ 1) (n : ℕ) : List RationalBeliefState :=
  List.ofFn fun i : Fin n =>
    restrictStateL (supportSentenceList S) (supportSentenceList_nodup S) (Q i) (hQ i)

/-- On days `< n` and sentences of `S`, the rational history of `restrictedPastL` is the table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma rationalHistory_restrictedPastL {S : Finset Sentence} {Q : ℕ → Sentence → ℚ}
    {hQ : ∀ k φ, 0 ≤ Q k φ ∧ Q k φ ≤ 1} {n k : ℕ} (hk : k < n) {φ : Sentence} (hφ : φ ∈ S) :
    rationalHistory (restrictedPastL S Q hQ n) k φ = Q k φ := by
  have hlen : k < (restrictedPastL S Q hQ n).length := by simp [restrictedPastL, hk]
  rw [rationalHistory_getElem _ hlen]
  simp only [restrictedPastL, List.getElem_ofFn]
  exact restrictStateL_quote_of_mem (mem_supportSentenceList.mpr hφ)

/-! ## Finite day records and the table they denote -/

/-- A day of the overlaid recursion as finite data: the core state and the mentioned set.
Source: [[bli-overlay-mandate]] T6
Kind: D
Fidelity: exact -/
structure OvRecord where
  /-- The day's core state. -/
  core : RationalBeliefState
  /-- The day's mentioned set (of the firm's strategy). -/
  mentioned : Finset Sentence

/-- The overlaid table denoted by a list of day records: on day `k` (inside the list) the core
quote on the mentioned set and the overlay elsewhere; `0` outside the list. This is where `ov`
is read, on finite data only.
Source: [[bli-overlay-mandate]] T6, D2
Kind: D
Fidelity: exact -/
def recTable (ov : Overlay) (recs : List OvRecord) : ℕ → Sentence → ℚ := fun k φ =>
  if hk : k < recs.length then
    if φ ∈ recs[k].mentioned then recs[k].core.quote φ
    else ov.val k ((recs.take k).map OvRecord.core) recs[k].core φ
  else 0

/-- `recTable` is in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma recTable_range (ov : Overlay) (recs : List OvRecord) :
    ∀ k φ, 0 ≤ recTable ov recs k φ ∧ recTable ov recs k φ ≤ 1 := by
  intro k φ
  unfold recTable
  by_cases hk : k < recs.length
  · rw [dif_pos hk]
    by_cases hφ : φ ∈ recs[k].mentioned
    · rw [if_pos hφ]
      exact recs[k].core.quote_mem_Icc φ
    · rw [if_neg hφ]
      exact ov.range _ _ _ _
  · rw [dif_neg hk]
    exact ⟨le_rfl, zero_le_one⟩

/-- The semantic prefix of day records, in append form.
Source: [[bli-overlay-mandate]] T6
Kind: D
Fidelity: exact -/
noncomputable def overlayRecPrefix (DP : DeductiveProcess) (ov : Overlay) : ℕ → List OvRecord
  | 0 => []
  | n + 1 => overlayRecPrefix DP ov n ++ [⟨coreState DP ov n, mentionedSet (firmStrat DP ov n)⟩]

/-- The prefix has length `n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma overlayRecPrefix_length (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    (overlayRecPrefix DP ov n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [overlayRecPrefix, ih]

/-- Inside the prefix, entry `m` is the day-`m` record.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma overlayRecPrefix_getD (DP : DeductiveProcess) (ov : Overlay) (d : OvRecord) {n m : ℕ}
    (hm : m < n) :
    (overlayRecPrefix DP ov n).getD m d = ⟨coreState DP ov m, mentionedSet (firmStrat DP ov m)⟩ := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [overlayRecPrefix]
      by_cases hmn : m < n
      · rw [List.getD_append _ _ _ _ (by simpa using hmn)]
        exact ih hmn
      · have hmeq : m = n := by omega
        subst m
        simp

/-- The append-form prefix is the `List.ofFn` form.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma overlayRecPrefix_eq_ofFn (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    overlayRecPrefix DP ov n =
      List.ofFn fun i : Fin n => (⟨coreState DP ov i, mentionedSet (firmStrat DP ov i)⟩ : OvRecord) := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp only [List.getElem_ofFn]
    rw [← List.getD_eq_getElem (overlayRecPrefix DP ov n)
      (⟨coreState DP ov 0, mentionedSet (firmStrat DP ov 0)⟩ : OvRecord) hi₁]
    apply overlayRecPrefix_getD
    simpa using hi₁

/-- The table denoted by the semantic prefix is the overlaid table, on days `< n`.
Source: [[bli-overlay-mandate]] T6
Kind: L
Fidelity: exact -/
lemma recTable_overlayRecPrefix (DP : DeductiveProcess) (ov : Overlay) {n k : ℕ} (hk : k < n)
    (φ : Sentence) : recTable ov (overlayRecPrefix DP ov n) k φ = overlayQuote DP ov k φ := by
  have hlen : k < (overlayRecPrefix DP ov n).length := by simpa using hk
  have hcore : (overlayRecPrefix DP ov n)[k].core = coreState DP ov k := by
    simp [overlayRecPrefix_eq_ofFn, List.getElem_ofFn]
  have hmen : (overlayRecPrefix DP ov n)[k].mentioned = mentionedSet (firmStrat DP ov k) := by
    simp [overlayRecPrefix_eq_ofFn, List.getElem_ofFn]
  have htake : ((overlayRecPrefix DP ov n).take k).map OvRecord.core = corePast DP ov k := by
    apply List.ext_getElem
    · simp [corePast, Nat.min_eq_left hk.le]
    · intro i hi₁ hi₂
      simp [corePast, overlayRecPrefix_eq_ofFn, List.getElem_ofFn]
  unfold recTable
  rw [dif_pos hlen, hcore, hmen, htake, overlayQuote_eq_ite]

/-! ## The bounded evaluator over an explicit stage table -/

/-- **The bounded evaluator.** Run `n` days of the overlaid recursion against an explicit stage
table `D` and one common market-maker search bound: on day `n`, the firm built from the table
of the records so far, the restricted past in the computable order, and `marketMakerSearchUpTo`.
Source: [[bli-overlay-mandate]] T6
Kind: D
Fidelity: exact -/
def overlayPrefixAtFuel (D : ℕ → Finset Sentence) (ov : Overlay) (fuel : ℕ) :
    ℕ → Option (List OvRecord)
  | 0 => some []
  | n + 1 => do
      let past ← overlayPrefixAtFuel D ov fuel n
      let state ← marketMakerSearchUpTo (TradingFirmAtFromStages D (recTable ov past) n)
        (restrictedPastL (mentionedSet (TradingFirmAtFromStages D (recTable ov past) n))
          (recTable ov past) (recTable_range ov past) n)
        (marketMakerError n) fuel
      some (past ++ [⟨state, mentionedSet (TradingFirmAtFromStages D (recTable ov past) n)⟩])

/-- The successor step, in explicit `Option.bind` form.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma overlayPrefixAtFuel_succ (D : ℕ → Finset Sentence) (ov : Overlay) (fuel n : ℕ) :
    overlayPrefixAtFuel D ov fuel (n + 1) =
      (overlayPrefixAtFuel D ov fuel n).bind fun past =>
        (marketMakerSearchUpTo (TradingFirmAtFromStages D (recTable ov past) n)
          (restrictedPastL (mentionedSet (TradingFirmAtFromStages D (recTable ov past) n))
            (recTable ov past) (recTable_range ov past) n)
          (marketMakerError n) fuel).bind fun state =>
          some (past ++ [⟨state, mentionedSet (TradingFirmAtFromStages D (recTable ov past) n)⟩]) :=
  rfl

/-- More fuel never changes a success.
Source: [[bli-overlay-mandate]] T6
Kind: L
Fidelity: exact -/
lemma overlayPrefixAtFuel_mono_success (D : ℕ → Finset Sentence) (ov : Overlay) (n : ℕ)
    {fuel fuel' : ℕ} {recs : List OvRecord} (hff : fuel ≤ fuel')
    (h : overlayPrefixAtFuel D ov fuel n = some recs) :
    overlayPrefixAtFuel D ov fuel' n = some recs := by
  induction n generalizing recs with
  | zero => simpa [overlayPrefixAtFuel] using h
  | succ n ih =>
      rw [overlayPrefixAtFuel_succ] at h ⊢
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨past, hpast, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨state, hstate, hout⟩ := h
      cases hout
      rw [ih hpast]
      simp only [Option.bind_some]
      rw [marketMakerSearchUpTo_mono_success _ _ _ hff hstate]
      rfl

/-- Some fuel succeeds, on every day.
Source: [[bli-overlay-mandate]] T6
Kind: L
Fidelity: exact -/
lemma exists_overlayPrefixAtFuel (D : ℕ → Finset Sentence) (ov : Overlay) (n : ℕ) :
    ∃ fuel recs, overlayPrefixAtFuel D ov fuel n = some recs := by
  induction n with
  | zero => exact ⟨0, [], rfl⟩
  | succ n ih =>
      obtain ⟨fuel₁, past, hpast⟩ := ih
      let T := TradingFirmAtFromStages D (recTable ov past) n
      let rp := restrictedPastL (mentionedSet T) (recTable ov past) (recTable_range ov past) n
      let fuel₂ := marketMakerIndex T rp (marketMakerError n) (marketMakerError_pos n) + 1
      let fuel := max fuel₁ fuel₂
      refine ⟨fuel, past ++ [⟨MarketMaker T rp (marketMakerError n) (marketMakerError_pos n),
        mentionedSet T⟩], ?_⟩
      rw [overlayPrefixAtFuel_succ,
        overlayPrefixAtFuel_mono_success D ov n (Nat.le_max_left fuel₁ fuel₂) hpast]
      change Option.bind (marketMakerSearchUpTo T rp (marketMakerError n) fuel)
        (fun state => some (past ++ [⟨state, mentionedSet T⟩])) = _
      rw [MarketMaker_search_of_clock_le T rp (marketMakerError n) (marketMakerError_pos n)
        (Nat.le_max_right fuel₁ fuel₂)]
      rfl

/-- **Soundness.** A success of the bounded evaluator, against a stage table agreeing with
`DP.D` below `n`, is the semantic prefix of the recursion: the records' cores are
`coreState DP ov i` and their mentioned sets are `mentionedSet (firmStrat DP ov i)`. The day
step's market maker is identified with `coreState_eq` through `MarketMaker_eq_of_eqOn_mentioned`
(the two restricted pasts list the same values in different orders).
Source: [[bli-overlay-mandate]] T6
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem overlayPrefixAtFuel_sound (DP : DeductiveProcess) (D : ℕ → Finset Sentence)
    (ov : Overlay) (fuel n : ℕ) (hD : ∀ m, m < n → D m = DP.D m) {recs : List OvRecord}
    (h : overlayPrefixAtFuel D ov fuel n = some recs) : recs = overlayRecPrefix DP ov n := by
  induction n generalizing recs with
  | zero =>
      simp [overlayPrefixAtFuel] at h
      subst recs
      rfl
  | succ n ih =>
      rw [overlayPrefixAtFuel_succ, Option.bind_eq_some_iff] at h
      obtain ⟨past, hpast, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨state, hstate, hout⟩ := h
      cases hout
      have hpastEq := ih (fun m hm => hD m (by omega)) hpast
      subst past
      have hfirm : TradingFirmAtFromStages D (recTable ov (overlayRecPrefix DP ov n)) n =
          firmStrat DP ov n := by
        rw [TradingFirmAtFromStages_eq_of_eq_prefix DP D _ n (fun m hm => hD m (by omega))]
        unfold firmStrat
        apply TradingFirmAt_eq_of_eq_prefix
        intro k hk φ
        exact recTable_overlayRecPrefix DP ov hk φ
      rw [hfirm] at hstate
      have hstateEq := MarketMaker_searchUpTo_sound _ _ _ (marketMakerError_pos n) hstate
      have hcore : state = coreState DP ov n := by
        rw [hstateEq, coreState_eq]
        apply MarketMaker_eq_of_eqOn_mentioned
        intro φ hφ k hk
        have hφ' := mem_mentionedSet_iff.mpr hφ
        unfold overlayRestrictedPast
        rw [rationalHistory_restrictedPastL hk hφ', rationalHistory_restrictedPast hk hφ']
        exact recTable_overlayRecPrefix DP ov hk φ
      rw [hcore, hfirm]
      rfl

/-! ## The process composite -/

/-- Decode the stages, then run the overlaid recursion under the same fuel.
Source: [[bli-overlay-mandate]] T6
Kind: D
Fidelity: exact -/
def overlayPrefixAtFuelP {DP : DeductiveProcess} (process : DeductiveProcessComputation DP)
    (ov : Overlay) (fuel n : ℕ) : Option (List OvRecord) := do
  let stages ← processStagePrefixAtFuel process fuel n
  overlayPrefixAtFuel (decodedStageTable stages) ov fuel n

/-- The composite, in explicit `Option.bind` form.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma overlayPrefixAtFuelP_def {DP : DeductiveProcess} (process : DeductiveProcessComputation DP)
    (ov : Overlay) (fuel n : ℕ) :
    overlayPrefixAtFuelP process ov fuel n =
      (processStagePrefixAtFuel process fuel n).bind fun stages =>
        overlayPrefixAtFuel (decodedStageTable stages) ov fuel n := rfl

/-- Soundness of the composite.
Source: [[bli-overlay-mandate]] T6
Kind: L
Fidelity: exact -/
lemma overlayPrefixAtFuelP_sound {DP : DeductiveProcess} (process : DeductiveProcessComputation DP)
    (ov : Overlay) (fuel n : ℕ) {recs : List OvRecord}
    (h : overlayPrefixAtFuelP process ov fuel n = some recs) : recs = overlayRecPrefix DP ov n := by
  rw [overlayPrefixAtFuelP_def, Option.bind_eq_some_iff] at h
  obtain ⟨stages, hstages, hrecs⟩ := h
  have hstageSound := processStagePrefixAtFuel_sound process fuel n hstages
  exact overlayPrefixAtFuel_sound DP (decodedStageTable stages) ov fuel n hstageSound.2 hrecs

/-- Some fuel succeeds for the composite.
Source: [[bli-overlay-mandate]] T6
Kind: L
Fidelity: exact -/
lemma exists_overlayPrefixAtFuelP {DP : DeductiveProcess} (process : DeductiveProcessComputation DP)
    (ov : Overlay) (n : ℕ) : ∃ fuel recs, overlayPrefixAtFuelP process ov fuel n = some recs := by
  obtain ⟨fuel₁, stages, hstages⟩ := exists_processStagePrefixAtFuel process n
  obtain ⟨fuel₂, recs, hrecs⟩ := exists_overlayPrefixAtFuel (decodedStageTable stages) ov n
  let fuel := max fuel₁ fuel₂
  refine ⟨fuel, recs, ?_⟩
  rw [overlayPrefixAtFuelP_def,
    processStagePrefixAtFuel_mono_success process n (Nat.le_max_left fuel₁ fuel₂) hstages]
  exact overlayPrefixAtFuel_mono_success (decodedStageTable stages) ov n
    (Nat.le_max_right fuel₁ fuel₂) hrecs

/-! ## The encoded quote evaluators -/

/-- The overlaid quote on sentence *codes*; malformed codes quote `0` (as `ComputableMarket`'s
total external table permits).
Source: [[bli-overlay-mandate]] T6
Kind: D
Fidelity: exact -/
noncomputable def overlayEncodedQuote (DP : DeductiveProcess) (ov : Overlay)
    (day sentenceCode : ℕ) : ℚ :=
  match Encodable.decode (α := Sentence) sentenceCode with
  | some φ => overlayQuote DP ov day φ
  | none => 0

/-- The bounded encoded quote evaluator: run the composite for `day + 1` days and read the
table at `(day, code)`.
Source: [[bli-overlay-mandate]] T6
Kind: D
Fidelity: exact -/
def overlayEncodedQuoteAtFuel {DP : DeductiveProcess} (process : DeductiveProcessComputation DP)
    (ov : Overlay) (fuel day sentenceCode : ℕ) : Option ℚ := do
  let recs ← overlayPrefixAtFuelP process ov fuel (day + 1)
  some <| match Encodable.decode (α := Sentence) sentenceCode with
    | some φ => recTable ov recs day φ
    | none => 0

/-- The evaluator, in explicit `Option.bind` form.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma overlayEncodedQuoteAtFuel_def {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (ov : Overlay) (fuel day sentenceCode : ℕ) :
    overlayEncodedQuoteAtFuel process ov fuel day sentenceCode =
      (overlayPrefixAtFuelP process ov fuel (day + 1)).bind fun recs =>
        some (match Encodable.decode (α := Sentence) sentenceCode with
          | some φ => recTable ov recs day φ
          | none => 0) := rfl

/-- Soundness of the encoded quote evaluator.
Source: [[bli-overlay-mandate]] T6
Kind: L
Fidelity: exact -/
lemma overlayEncodedQuoteAtFuel_sound {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (ov : Overlay) {fuel day sentenceCode : ℕ} {q : ℚ}
    (h : overlayEncodedQuoteAtFuel process ov fuel day sentenceCode = some q) :
    q = overlayEncodedQuote DP ov day sentenceCode := by
  rw [overlayEncodedQuoteAtFuel_def, Option.bind_eq_some_iff] at h
  obtain ⟨recs, hrecs, h⟩ := h
  have hrecsEq := overlayPrefixAtFuelP_sound process ov fuel (day + 1) hrecs
  subst recs
  cases hdecode : Encodable.decode (α := Sentence) sentenceCode with
  | none => simpa [overlayEncodedQuote, hdecode] using h.symm
  | some φ =>
      simp only [hdecode, Option.some.injEq] at h
      rw [recTable_overlayRecPrefix DP ov (Nat.lt_succ_self day)] at h
      simpa [overlayEncodedQuote, hdecode] using h.symm

/-- Some fuel succeeds for the encoded quote evaluator, with the exact quote.
Source: [[bli-overlay-mandate]] T6
Kind: L
Fidelity: exact -/
lemma exists_overlayEncodedQuoteAtFuel {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (ov : Overlay) (day sentenceCode : ℕ) :
    ∃ fuel, overlayEncodedQuoteAtFuel process ov fuel day sentenceCode =
      some (overlayEncodedQuote DP ov day sentenceCode) := by
  obtain ⟨fuel, recs, hrecs⟩ := exists_overlayPrefixAtFuelP process ov (day + 1)
  have hrecsEq := overlayPrefixAtFuelP_sound process ov fuel (day + 1) hrecs
  subst recs
  refine ⟨fuel, ?_⟩
  rw [overlayEncodedQuoteAtFuel_def, hrecs]
  simp only [Option.bind_some]
  cases hdecode : Encodable.decode (α := Sentence) sentenceCode with
  | none => simp [overlayEncodedQuote, hdecode]
  | some φ => simp [overlayEncodedQuote, hdecode, recTable_overlayRecPrefix DP ov (Nat.lt_succ_self day)]

/-- The natural-coded evaluator in `Partrec.rfindOpt`'s argument order: the paired input is
`(day, sentenceCode)`, the search variable is the fuel.
Source: [[bli-overlay-mandate]] T6
Kind: D
Fidelity: exact -/
def overlayEncodedQuoteNatAtFuel {DP : DeductiveProcess} (process : DeductiveProcessComputation DP)
    (ov : Overlay) (z fuel : ℕ) : Option ℕ :=
  (overlayEncodedQuoteAtFuel process ov fuel z.unpair.1 z.unpair.2).map Encodable.encode

/-- Soundness of the natural-coded evaluator.
Source: [[bli-overlay-mandate]] T6
Kind: L
Fidelity: exact -/
lemma overlayEncodedQuoteNatAtFuel_sound {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (ov : Overlay) {z fuel out : ℕ}
    (h : overlayEncodedQuoteNatAtFuel process ov z fuel = some out) :
    out = Encodable.encode (overlayEncodedQuote DP ov z.unpair.1 z.unpair.2) := by
  unfold overlayEncodedQuoteNatAtFuel at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨q, hq, rfl⟩ := h
  rw [overlayEncodedQuoteAtFuel_sound process ov hq]

/-- Some fuel succeeds for the natural-coded evaluator.
Source: [[bli-overlay-mandate]] T6
Kind: L
Fidelity: exact -/
lemma exists_overlayEncodedQuoteNatAtFuel {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (ov : Overlay) (z : ℕ) :
    ∃ fuel, overlayEncodedQuoteNatAtFuel process ov z fuel =
      some (Encodable.encode (overlayEncodedQuote DP ov z.unpair.1 z.unpair.2)) := by
  obtain ⟨fuel, hfuel⟩ := exists_overlayEncodedQuoteAtFuel process ov z.unpair.1 z.unpair.2
  refine ⟨fuel, ?_⟩
  unfold overlayEncodedQuoteNatAtFuel
  rw [hfuel]
  rfl

/-! ## The compiler boundary -/

/-- **The compiler boundary (not instantiated).** The one structure asserting that the bounded
evaluator is a computable two-argument natural function — the shape of FAF's
`LIABoundedEvaluatorCompiler`. It carries no market correctness, range, exploitation or
logical-inductor conclusion. Instantiating it is the primitive-recursive compilation of the day
step (FAF's `LIACompiler.lean` does this for the LIA in 4041 lines) and is where `ov`'s
computability would enter, as a computable function of the encoded finite records; it was not
attempted here.
Source: [[bli-overlay-mandate]] T6
Kind: D
Fidelity: exact -/
structure OverlayBoundedEvaluatorCompiler {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (ov : Overlay) where
  /-- The bounded evaluator is computable. -/
  computable : Computable₂ (overlayEncodedQuoteNatAtFuel process ov)

/-- Generic minimization turns a compiler for the bounded evaluator into one total computable
exact quote function.
Source: [[bli-overlay-mandate]] T6
Kind: L
Fidelity: exact -/
lemma OverlayBoundedEvaluatorCompiler.quote_computable {DP : DeductiveProcess}
    {process : DeductiveProcessComputation DP} {ov : Overlay}
    (compiler : OverlayBoundedEvaluatorCompiler process ov) :
    Computable (fun z : ℕ => Encodable.encode (overlayEncodedQuote DP ov z.unpair.1 z.unpair.2)) := by
  let search : ℕ → Part ℕ := fun z => Nat.rfindOpt (overlayEncodedQuoteNatAtFuel process ov z)
  have hsearch : Partrec search := Partrec.rfindOpt compiler.computable
  apply hsearch.of_eq_tot
  intro z
  have hdom : (search z).Dom := by
    rw [Nat.rfindOpt_dom]
    obtain ⟨fuel, hfuel⟩ := exists_overlayEncodedQuoteNatAtFuel process ov z
    exact ⟨fuel, _, hfuel⟩
  let out := (search z).get hdom
  have hout : out ∈ search z := Part.get_mem hdom
  obtain ⟨fuel, hfuel⟩ := Nat.rfindOpt_spec hout
  have houtEq := overlayEncodedQuoteNatAtFuel_sound process ov hfuel
  rw [← houtEq]
  exact hout

/-- The partial-recursive quote program `ComputableMarket` asks for, from the boundary.
Source: [[bli-overlay-mandate]] T6
Kind: L
Fidelity: exact -/
lemma OverlayBoundedEvaluatorCompiler.exists_quote_code {DP : DeductiveProcess}
    {process : DeductiveProcessComputation DP} {ov : Overlay}
    (compiler : OverlayBoundedEvaluatorCompiler process ov) :
    ∃ code : Nat.Partrec.Code, ∀ z : ℕ,
      Encodable.encode (overlayEncodedQuote DP ov z.unpair.1 z.unpair.2) ∈ code.eval z := by
  have hcomp := compiler.quote_computable
  have hpart : Nat.Partrec (fun z : ℕ =>
      Part.some (Encodable.encode (overlayEncodedQuote DP ov z.unpair.1 z.unpair.2))) :=
    Partrec.nat_iff.mp hcomp.partrec
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp hpart
  refine ⟨code, ?_⟩
  intro z
  rw [hcode]
  simp

/-- **From the boundary to `ComputableMarket`.** Once the bounded evaluator is compiled, the
overlaid market has the exact rational market program the criterion asks for. This is the
reduction; the boundary itself is not instantiated (see the structure's docstring).
Source: [[bli-overlay-mandate]] T6; [[bli-program]] §7 item 8
Kind: L
Fidelity: weaker: conditional on the (uninstantiated) compiler boundary
Hyps: (b) `compiler : OverlayBoundedEvaluatorCompiler process ov` — the compilation
certificate, not proved here -/
theorem OverlayBoundedEvaluatorCompiler.toComputableMarket {DP : DeductiveProcess}
    {process : DeductiveProcessComputation DP} {ov : Overlay}
    (compiler : OverlayBoundedEvaluatorCompiler process ov) :
    ComputableMarket (overlayHistory DP ov) := by
  obtain ⟨code, hcode⟩ := compiler.exists_quote_code
  refine ⟨overlayHistory_range DP ov, overlayEncodedQuote DP ov, code, ?_, hcode⟩
  intro n φ
  simp [overlayHistory, overlayEncodedQuote, Encodable.encodek]

/-- **Criterion assembly from the boundary**: with a compiled evaluator, the overlaid market is
a logical inductor. The boundary is the one missing piece (L6(b)); nothing else is assumed.
Source: [[bli-overlay-mandate]] T6
Kind: L
Fidelity: weaker: conditional on the (uninstantiated) compiler boundary
Hyps: (b) `compiler` as in `toComputableMarket` -/
theorem overlay_isLogicalInductor_of_compiler {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (ov : Overlay)
    (compiler : OverlayBoundedEvaluatorCompiler process ov) :
    IsLogicalInductor (overlayHistory DP ov) DP :=
  overlay_isLogicalInductor_of_computableMarket DP ov process.toComputable
    compiler.toComputableMarket

end Cleanroom.Bli.BliOverlay.AttemptA
