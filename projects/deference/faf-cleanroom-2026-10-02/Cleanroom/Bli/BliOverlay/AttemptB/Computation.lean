import Cleanroom.Bli.BliOverlay.AttemptB.Recursion
import LogicalInduction.Construction.LIAComputation

/-!
# `bli-overlay` (attempt B) · Computation: the bounded evaluator of the overlaid recursion (T6, stretch)

The shape of FAF's `Construction/LIAComputation.lean`, for the overlaid recursion:

* `prefixTable D ov states` — the overlaid table read off a **core prefix** (the list of core
  states): on a day `k` inside the prefix it decides membership in the mentioned set of the
  day-`k` firm built (from the explicit stage table `D`) on the table below `k`, and returns the
  prefix state's quote or the overlay's value. It is what `overlayQuote` is once the core states
  are known (`prefixTable_corePrefix`).
* `overlayPrefixAtFuel D ov fuel n : Option (List RationalBeliefState)` — `n` days of the exact
  finite recurrence with one common `marketMakerSearchUpTo` clock, on the **substituted** firm
  (angle B); the three-lemma shape *monotone in fuel* / *sound* (a success is the core prefix
  `corePrefix DP ov n`, given the stage table agrees with `DP.D` below `n`) / *eventually
  successful*.
* `overlayQuoteAtFuel` / `overlayEncodedQuote` — the day-`n` quote of a sentence *code*
  (malformed codes quote `0`), sound and eventually successful; `overlayQuoteNatAtFuel` the
  `ℕ`-coded rung in `Partrec.rfindOpt`'s argument order.
* `OverlayBoundedEvaluatorCompiler DP ov D` — **the compiler boundary**: a stage table equal to
  `DP.D` and a `Computable₂` certificate for the bounded evaluator. From it,
  `toComputableMarket : ComputableMarket (overlayHistory DP ov)` by the `rfindOpt` argument of
  FAF's `LIABoundedEvaluatorCompiler.quote_computable`, and `overlay_isLogicalInductor_of_compiler`.

**What is not here (OPEN, recorded in the report):** an instantiation of the boundary. FAF
instantiates its own boundary in `LIACompiler.lean` (4041 lines, never imported here) by a
primitive-recursive compilation of the trade-list rung of its evaluator. The overlaid evaluator
additionally needs (i) `ov` given by a computable function of encoded finite data and (ii) the
`mentionedSet` scan and `Strategy.substPast` compiled — nothing below claims any of it.
-/

namespace Cleanroom.Bli.BliOverlay.AttemptB

open LogicalInduction Cleanroom.Bli.BliFound

/-! ## The overlaid table of a core prefix -/

/-- **The overlaid table read off a core prefix.** On day `k` with `states[k]? = some B`: the
firm is built from `D` on the table below `k` (recursively); `B.quote φ` if `φ` is in its
mentioned set, `ov.val k (states.take k) B φ` otherwise; `0` beyond the prefix.
Source: [[bli-overlay-mandate]] T6
Kind: D
Fidelity: exact -/
def prefixTable (D : ℕ → Finset Sentence) (ov : Overlay) (states : List RationalBeliefState) :
    ℕ → Sentence → ℚ
  | k => fun φ =>
      match states[k]? with
      | some B =>
          if φ ∈ mentionedSet (TradingFirmAtFromStages D
              (fun j ψ => if _h : j < k then prefixTable D ov states j ψ else 0) k)
          then B.quote φ else ov.val k (states.take k) B φ
      | none => 0
termination_by k => k
decreasing_by
  all_goals exact _h

/-- The one-step unfolding of `prefixTable`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prefixTable_eq (D : ℕ → Finset Sentence) (ov : Overlay) (states : List RationalBeliefState)
    (k : ℕ) (φ : Sentence) :
    prefixTable D ov states k φ =
      match states[k]? with
      | some B =>
          if φ ∈ mentionedSet (TradingFirmAtFromStages D
              (fun j ψ => if j < k then prefixTable D ov states j ψ else 0) k)
          then B.quote φ else ov.val k (states.take k) B φ
      | none => 0 := by
  rw [prefixTable]
  rfl

/-- `prefixTable` inside the prefix.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prefixTable_of_some (D : ℕ → Finset Sentence) (ov : Overlay)
    (states : List RationalBeliefState) {k : ℕ} {B : RationalBeliefState}
    (h : states[k]? = some B) (φ : Sentence) :
    prefixTable D ov states k φ =
      if φ ∈ mentionedSet (TradingFirmAtFromStages D
          (fun j ψ => if j < k then prefixTable D ov states j ψ else 0) k)
      then B.quote φ else ov.val k (states.take k) B φ := by
  rw [prefixTable_eq, h]

/-- `prefixTable` beyond the prefix is `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prefixTable_of_none (D : ℕ → Finset Sentence) (ov : Overlay)
    (states : List RationalBeliefState) {k : ℕ} (h : states[k]? = none) (φ : Sentence) :
    prefixTable D ov states k φ = 0 := by
  rw [prefixTable_eq, h]

/-! ## The bounded evaluator -/

/-- **The bounded evaluator**: `n` days of the exact finite overlaid recurrence (angle B: the
market maker's search on the past-substituted firm) with an explicit stage table and one common
search clock.
Source: [[bli-overlay-mandate]] T6 (`overlayPrefixAtFuel`)
Kind: D
Fidelity: exact -/
def overlayPrefixAtFuel (D : ℕ → Finset Sentence) (ov : Overlay) (fuel : ℕ) :
    ℕ → Option (List RationalBeliefState)
  | 0 => some []
  | n + 1 => do
      let past ← overlayPrefixAtFuel D ov fuel n
      let state ← marketMakerSearchUpTo
        (Strategy.substPast (prefixTable D ov past)
          (TradingFirmAtFromStages D (prefixTable D ov past) n))
        past (marketMakerError n) fuel
      some (past ++ [state])

/-- The successor step of `overlayPrefixAtFuel`, in explicit `Option.bind` form.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma overlayPrefixAtFuel_succ (D : ℕ → Finset Sentence) (ov : Overlay) (fuel n : ℕ) :
    overlayPrefixAtFuel D ov fuel (n + 1) =
      (overlayPrefixAtFuel D ov fuel n).bind fun past =>
        (marketMakerSearchUpTo
          (Strategy.substPast (prefixTable D ov past)
            (TradingFirmAtFromStages D (prefixTable D ov past) n))
          past (marketMakerError n) fuel).bind fun state => some (past ++ [state]) := rfl

/-- Monotone in fuel: a success at `fuel` is a success at every larger fuel, with the same value.
Source: [[bli-overlay-mandate]] T6 (`_mono_success`)
Kind: L
Fidelity: exact -/
lemma overlayPrefixAtFuel_mono_success (D : ℕ → Finset Sentence) (ov : Overlay) (n : ℕ)
    {fuel fuel' : ℕ} {states : List RationalBeliefState} (hff : fuel ≤ fuel')
    (h : overlayPrefixAtFuel D ov fuel n = some states) :
    overlayPrefixAtFuel D ov fuel' n = some states := by
  induction n generalizing states with
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

/-! ## The core prefix and soundness -/

/-- The append-form prefix of the core states.
Source: none: infrastructure (FAF's `liaStatePrefix` shape)
Kind: D
Fidelity: exact -/
noncomputable def corePrefix (DP : DeductiveProcess) (ov : Overlay) : ℕ → List RationalBeliefState
  | 0 => []
  | n + 1 => corePrefix DP ov n ++ [coreState DP ov n]

/-- The `n`-day prefix has `n` entries.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma corePrefix_length (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    (corePrefix DP ov n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [corePrefix, ih]

/-- The append-form prefix is the `List.ofFn` core past.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma corePrefix_eq_corePast (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    corePrefix DP ov n = corePast DP ov n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [corePrefix, ih]
      unfold corePast
      rw [List.ofFn_succ', List.concat_eq_append]
      rfl

/-- Inside the prefix, `[k]?` is the day-`k` core state.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma corePrefix_getElem? (DP : DeductiveProcess) (ov : Overlay) {n k : ℕ} (hk : k < n) :
    (corePrefix DP ov n)[k]? = some (coreState DP ov k) := by
  rw [corePrefix_eq_corePast]
  simp [corePast, hk]

/-- Taking `k ≤ n` days of the `n`-day prefix is the `k`-day prefix.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma corePrefix_take (DP : DeductiveProcess) (ov : Overlay) {n k : ℕ} (hk : k ≤ n) :
    (corePrefix DP ov n).take k = corePrefix DP ov k := by
  induction n with
  | zero =>
      have : k = 0 := by omega
      subst this
      rfl
  | succ n ih =>
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · rw [corePrefix, List.take_append_of_le_length (by simp; omega)]
        exact ih (by omega)
      · have : k = n + 1 := by omega
        subst this
        exact List.take_of_length_le (by simp)

/-- **`prefixTable` on the core prefix is the overlaid table**, on every day inside the prefix,
when the stage table agrees with the process below `n`.
Source: [[bli-overlay-mandate]] T6
Kind: L
Fidelity: exact -/
theorem prefixTable_corePrefix (DP : DeductiveProcess) (D : ℕ → Finset Sentence) (ov : Overlay)
    (n : ℕ) (hD : ∀ m, m < n → D m = DP.D m) :
    ∀ k, k < n → ∀ φ, prefixTable D ov (corePrefix DP ov n) k φ = overlayQuote DP ov k φ := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk φ
      rw [prefixTable_of_some D ov _ (corePrefix_getElem? DP ov hk)]
      have hbelow : (fun j ψ => if j < k then prefixTable D ov (corePrefix DP ov n) j ψ else 0) =
          quoteBelow DP ov k := by
        funext j ψ
        unfold quoteBelow
        split_ifs with hj
        · exact ih j hj (by omega) ψ
        · rfl
      have hfirm : TradingFirmAtFromStages D
          (fun j ψ => if j < k then prefixTable D ov (corePrefix DP ov n) j ψ else 0) k =
          firmStrat DP ov k := by
        rw [hbelow]
        unfold firmStrat
        exact TradingFirmAtFromStages_eq_of_eq_prefix DP D _ k (fun m hm => hD m (by omega))
      rw [hfirm, overlayQuote_eq, corePrefix_take DP ov hk.le, corePrefix_eq_corePast]

/-- **Soundness.** A successful bounded run is the core prefix, when the stage table agrees with the
process below `n`: the fuel affects termination only, never the result.
Source: [[bli-overlay-mandate]] T6 (`_sound`)
Kind: C
Fidelity: exact
Hyps: (a) — `MarketMaker_searchUpTo_sound`, `TradingFirmAtFromStages_eq_of_eq_prefix` are FAF theorems, applied -/
theorem overlayPrefixAtFuel_sound (DP : DeductiveProcess) (D : ℕ → Finset Sentence) (ov : Overlay)
    (fuel n : ℕ) (hD : ∀ m, m < n → D m = DP.D m) {states : List RationalBeliefState}
    (h : overlayPrefixAtFuel D ov fuel n = some states) : states = corePrefix DP ov n := by
  induction n generalizing states with
  | zero =>
      simp [overlayPrefixAtFuel] at h
      subst states
      rfl
  | succ n ih =>
      rw [overlayPrefixAtFuel_succ, Option.bind_eq_some_iff] at h
      obtain ⟨past, hpast, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨state, hstate, hout⟩ := h
      cases hout
      have hpastEq := ih (fun m hm => hD m (by omega)) hpast
      subst past
      have htable : prefixTable D ov (corePrefix DP ov n) = quoteBelow DP ov n := by
        funext k φ
        unfold quoteBelow
        split_ifs with hk
        · exact prefixTable_corePrefix DP D ov n (fun m hm => hD m (by omega)) k hk φ
        · apply prefixTable_of_none
          rw [List.getElem?_eq_none_iff]
          simpa using hk
      have hfirm : TradingFirmAtFromStages D (prefixTable D ov (corePrefix DP ov n)) n =
          firmStrat DP ov n := by
        rw [htable]
        unfold firmStrat
        exact TradingFirmAtFromStages_eq_of_eq_prefix DP D _ n (fun m hm => hD m (by omega))
      have hstateEq := MarketMaker_searchUpTo_sound _ (corePrefix DP ov n) (marketMakerError n)
        (marketMakerError_pos n) hstate
      rw [hfirm, htable, corePrefix_eq_corePast] at hstateEq
      have hcore : state = coreState DP ov n := by
        rw [coreState_eq]
        exact hstateEq
      rw [hcore]
      rfl

/-- Eventually successful: some fuel runs `n` days.
Source: [[bli-overlay-mandate]] T6 (`exists_`)
Kind: L
Fidelity: exact -/
theorem exists_overlayPrefixAtFuel (D : ℕ → Finset Sentence) (ov : Overlay) (n : ℕ) :
    ∃ fuel states, overlayPrefixAtFuel D ov fuel n = some states := by
  induction n with
  | zero => exact ⟨0, [], rfl⟩
  | succ n ih =>
      obtain ⟨fuel₁, past, hpast⟩ := ih
      let T := Strategy.substPast (prefixTable D ov past)
        (TradingFirmAtFromStages D (prefixTable D ov past) n)
      let fuel₂ := marketMakerIndex T past (marketMakerError n) (marketMakerError_pos n) + 1
      let fuel := max fuel₁ fuel₂
      refine ⟨fuel, past ++ [MarketMaker T past (marketMakerError n) (marketMakerError_pos n)], ?_⟩
      rw [overlayPrefixAtFuel_succ,
        overlayPrefixAtFuel_mono_success D ov n (Nat.le_max_left fuel₁ fuel₂) hpast]
      change Option.bind (marketMakerSearchUpTo T past (marketMakerError n) fuel)
        (fun state => some (past ++ [state])) = _
      rw [MarketMaker_search_of_clock_le T past (marketMakerError n) (marketMakerError_pos n)
        (Nat.le_max_right fuel₁ fuel₂)]
      rfl

/-! ## The day quote of a sentence code -/

/-- The overlaid exact quote on arbitrary natural sentence codes; malformed codes quote `0`.
Source: [[bli-overlay-mandate]] T6 (FAF's `liaEncodedQuote` shape)
Kind: D
Fidelity: exact -/
noncomputable def overlayEncodedQuote (DP : DeductiveProcess) (ov : Overlay) (day code : ℕ) : ℚ :=
  match Encodable.decode (α := Sentence) code with
  | some φ => overlayQuote DP ov day φ
  | none => 0

/-- The bounded day-quote evaluator: run `day + 1` days, then read the overlaid table of the prefix
at the decoded sentence.
Source: [[bli-overlay-mandate]] T6
Kind: D
Fidelity: exact -/
def overlayQuoteAtFuel (D : ℕ → Finset Sentence) (ov : Overlay) (fuel day code : ℕ) : Option ℚ := do
  let states ← overlayPrefixAtFuel D ov fuel (day + 1)
  some (match Encodable.decode (α := Sentence) code with
    | some φ => prefixTable D ov states day φ
    | none => 0)

/-- `overlayQuoteAtFuel` in explicit `Option.bind` form.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma overlayQuoteAtFuel_def (D : ℕ → Finset Sentence) (ov : Overlay) (fuel day code : ℕ) :
    overlayQuoteAtFuel D ov fuel day code =
      (overlayPrefixAtFuel D ov fuel (day + 1)).bind fun states =>
        some (match Encodable.decode (α := Sentence) code with
          | some φ => prefixTable D ov states day φ
          | none => 0) := rfl

/-- Soundness of the day-quote evaluator.
Source: [[bli-overlay-mandate]] T6
Kind: C
Fidelity: exact -/
theorem overlayQuoteAtFuel_sound (DP : DeductiveProcess) (D : ℕ → Finset Sentence) (ov : Overlay)
    {fuel day code : ℕ} (hD : ∀ m, m < day + 1 → D m = DP.D m) {q : ℚ}
    (h : overlayQuoteAtFuel D ov fuel day code = some q) :
    q = overlayEncodedQuote DP ov day code := by
  rw [overlayQuoteAtFuel_def, Option.bind_eq_some_iff] at h
  obtain ⟨states, hstates, h⟩ := h
  have hs := overlayPrefixAtFuel_sound DP D ov fuel (day + 1) hD hstates
  subst states
  rw [Option.some.injEq] at h
  rw [← h]
  unfold overlayEncodedQuote
  cases hdec : Encodable.decode (α := Sentence) code with
  | none => rfl
  | some φ => exact prefixTable_corePrefix DP D ov (day + 1) hD day (Nat.lt_succ_self day) φ

/-- The day-quote evaluator eventually succeeds with the overlaid quote.
Source: [[bli-overlay-mandate]] T6
Kind: L
Fidelity: exact -/
theorem exists_overlayQuoteAtFuel (DP : DeductiveProcess) (D : ℕ → Finset Sentence) (ov : Overlay)
    (day code : ℕ) (hD : ∀ m, m < day + 1 → D m = DP.D m) :
    ∃ fuel, overlayQuoteAtFuel D ov fuel day code = some (overlayEncodedQuote DP ov day code) := by
  obtain ⟨fuel, states, hstates⟩ := exists_overlayPrefixAtFuel D ov (day + 1)
  refine ⟨fuel, ?_⟩
  have hs := overlayPrefixAtFuel_sound DP D ov fuel (day + 1) hD hstates
  subst states
  rw [overlayQuoteAtFuel_def, hstates]
  simp only [Option.bind_some, Option.some.injEq]
  unfold overlayEncodedQuote
  cases hdec : Encodable.decode (α := Sentence) code with
  | none => rfl
  | some φ => exact prefixTable_corePrefix DP D ov (day + 1) hD day (Nat.lt_succ_self day) φ

/-- The `ℕ`-coded rung in `Partrec.rfindOpt`'s argument order: paired input `(day, code)`, the
search variable is the fuel.
Source: [[bli-overlay-mandate]] T6 (FAF's `liaEncodedQuoteNatAtFuel` shape)
Kind: D
Fidelity: exact -/
def overlayQuoteNatAtFuel (D : ℕ → Finset Sentence) (ov : Overlay) (z fuel : ℕ) : Option ℕ :=
  (overlayQuoteAtFuel D ov fuel z.unpair.1 z.unpair.2).map Encodable.encode

/-- Soundness of the `ℕ`-coded rung.
Source: [[bli-overlay-mandate]] T6
Kind: L
Fidelity: exact -/
lemma overlayQuoteNatAtFuel_sound (DP : DeductiveProcess) (D : ℕ → Finset Sentence) (ov : Overlay)
    (hD : ∀ m, D m = DP.D m) {z fuel out : ℕ}
    (h : overlayQuoteNatAtFuel D ov z fuel = some out) :
    out = Encodable.encode (overlayEncodedQuote DP ov z.unpair.1 z.unpair.2) := by
  unfold overlayQuoteNatAtFuel at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨q, hq, rfl⟩ := h
  rw [overlayQuoteAtFuel_sound DP D ov (fun m _ => hD m) hq]

/-- The `ℕ`-coded rung eventually succeeds.
Source: [[bli-overlay-mandate]] T6
Kind: L
Fidelity: exact -/
lemma exists_overlayQuoteNatAtFuel (DP : DeductiveProcess) (D : ℕ → Finset Sentence) (ov : Overlay)
    (hD : ∀ m, D m = DP.D m) (z : ℕ) :
    ∃ fuel, overlayQuoteNatAtFuel D ov z fuel =
      some (Encodable.encode (overlayEncodedQuote DP ov z.unpair.1 z.unpair.2)) := by
  obtain ⟨fuel, hfuel⟩ := exists_overlayQuoteAtFuel DP D ov z.unpair.1 z.unpair.2 (fun m _ => hD m)
  refine ⟨fuel, ?_⟩
  unfold overlayQuoteNatAtFuel
  rw [hfuel]
  rfl

/-! ## The compiler boundary -/

/-- **The compiler boundary of the overlaid recursion.** A stage table equal to the process's and a
`Computable₂` certificate for the bounded `ℕ`-coded evaluator. It carries no market correctness,
range, exploitation or logical-inductor conclusion; **it is not instantiated here** (OPEN: an
instantiation needs `ov` computable on encoded finite data and a compilation of the evaluator, the
work FAF's `LIACompiler.lean` does for its own boundary).
Source: [[bli-overlay-mandate]] T6 (the shape of FAF's `LIABoundedEvaluatorCompiler`)
Kind: D
Fidelity: exact -/
structure OverlayBoundedEvaluatorCompiler (DP : DeductiveProcess) (ov : Overlay)
    (D : ℕ → Finset Sentence) where
  /-- The stage table is the process's. -/
  stages : ∀ m, D m = DP.D m
  /-- The bounded evaluator is a computable two-argument natural function. -/
  computable : Computable₂ (overlayQuoteNatAtFuel D ov)

/-- Generic minimization turns a compiler for the bounded evaluator into a total computable
exact-quote function (FAF's `LIABoundedEvaluatorCompiler.quote_computable` argument).
Source: [[bli-overlay-mandate]] T6
Kind: C
Fidelity: exact
Hyps: (a) given the boundary structure -/
lemma OverlayBoundedEvaluatorCompiler.quote_computable {DP : DeductiveProcess} {ov : Overlay}
    {D : ℕ → Finset Sentence} (c : OverlayBoundedEvaluatorCompiler DP ov D) :
    Computable (fun z : ℕ => Encodable.encode (overlayEncodedQuote DP ov z.unpair.1 z.unpair.2)) := by
  let search : ℕ → Part ℕ := fun z => Nat.rfindOpt (overlayQuoteNatAtFuel D ov z)
  have hsearch : Partrec search := Partrec.rfindOpt c.computable
  apply hsearch.of_eq_tot
  intro z
  have hdom : (search z).Dom := by
    rw [Nat.rfindOpt_dom]
    obtain ⟨fuel, hfuel⟩ := exists_overlayQuoteNatAtFuel DP D ov c.stages z
    exact ⟨fuel, _, hfuel⟩
  let out := (search z).get hdom
  have hout : out ∈ search z := Part.get_mem hdom
  obtain ⟨fuel, hfuel⟩ := Nat.rfindOpt_spec hout
  have houtEq := overlayQuoteNatAtFuel_sound DP D ov c.stages hfuel
  rw [← houtEq]
  exact hout

/-- **T6, conditional form.** Once the boundary is instantiated, the overlaid recursion is a
computable market in FAF's sense (`ComputableMarket.ofComputableTable` at `overlayEncodedQuote`).
Source: [[bli-overlay-mandate]] T6 (`toComputableMarket`)
Kind: C
Fidelity: weaker: conditional on the (uninstantiated) boundary
Hyps: (a) given the boundary structure `c`; the boundary itself is OPEN -/
theorem OverlayBoundedEvaluatorCompiler.toComputableMarket {DP : DeductiveProcess} {ov : Overlay}
    {D : ℕ → Finset Sentence} (c : OverlayBoundedEvaluatorCompiler DP ov D) :
    ComputableMarket (overlayHistory DP ov) :=
  ComputableMarket.ofComputableTable (overlayEncodedQuote DP ov) (overlayHistory_range DP ov)
    (fun n φ => by simp [overlayHistory, overlayEncodedQuote, Encodable.encodek])
    c.quote_computable

/-- **L6 assembled from the boundary**: `IsLogicalInductor` for the overlaid recursion, given a
computable process and an instantiated evaluator compiler. Not L6: the boundary is open.
Source: [[bli-overlay-mandate]] T6 (mirrors FAF's `lia_isLogicalInductor_of_compiler`)
Kind: L
Fidelity: weaker: conditional on the (uninstantiated) boundary
Hyps: (a) given `hDP` and `c` -/
theorem overlay_isLogicalInductor_of_compiler {DP : DeductiveProcess} {ov : Overlay}
    {D : ℕ → Finset Sentence} (hDP : ComputableDeductiveProcess DP)
    (c : OverlayBoundedEvaluatorCompiler DP ov D) :
    IsLogicalInductor (overlayHistory DP ov) DP :=
  overlay_isLogicalInductor_of_computableMarket DP ov hDP c.toComputableMarket

end Cleanroom.Bli.BliOverlay.AttemptB
