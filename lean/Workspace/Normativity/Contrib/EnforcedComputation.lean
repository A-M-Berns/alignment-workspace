/-
# The modified market is computable, at the source's own boundary

`DeductiveEnforcement` leaves `ComputableMarket (history DP E)` as a premise.  That is
too weak a place to stop: an arbitrary `AdaptiveTrader` is an arbitrary Lean function and
carries no reason to be computable, so the premise is not merely unproved, it is
unprovable at that generality.

This file removes the premise for enforcers that are given **as effective data**.  An
`EffectiveEnforcer` is a function from the day and the ordinary aggregate's trade list to
the enforcement trade list — finite syntax in, finite syntax out.  The modified recursive
market is then computed by a bounded evaluator built exactly like the source's, and the
remaining obligation is the same one the source isolates for its own recurrence:

    `Computable₂ (enfEncodedQuoteNatAtFuel process E)`

`LIAComputation.lean` states that boundary for ordinary LIA as
`LIABoundedEvaluatorCompiler`, and `LIACompiler.lean` discharges it.  Every definition and
proof below is the same construction with one extra trade list appended to the day's
aggregate, which is why the shape matches line for line.

**What this does and does not close.**  It closes the reduction: given the bounded
evaluator's computability, the modified market is computable and the deductive market is a
logical inductor *in the source's original sense*, with no `ComputableMarket` premise.  It
does not discharge that computability, and `ROUND.md` records exactly why: the source's
primitive-recursive lemmas for its own recurrence — `marketMakerSearchUpToTradeList_prim`
and `tradingFirmTradesFromStageTradeLists_prim` — are `private` in `LIACompiler.lean`, so
they cannot be reused from here.  That is a module-visibility obstruction, not a
mathematical one.

Names are provisional (`AGENTS.md` standard 6).
-/

import LogicalInduction.Construction.LIAComputation
import Workspace.Normativity.Contrib.ProjectionCalibrated

namespace Workspace.Normativity.Contrib.EnforcedComputation

open LogicalInduction
open Workspace.Normativity.Contrib.DeductiveEnforcement

/-! ## Enforcers given as effective data

The enforcement trade list is computed from the day, **the day's deductive stage**, and the
ordinary aggregate's trade list.  The day-`n` intensity needs the ordinary aggregate's
`absBound`, which is a function of its trade list; and an enforcer whose constraint is a
*region derived from the deductive state* needs the stage.

The stage argument is what keeps the construction free of an extra computability
hypothesis, so it is worth saying why.  A region read off the day's stage would otherwise
force `Primrec (fun n => DP.D n)` on the caller, and the pinned source's
`DeductiveProcessComputation` does **not** supply that: it is a partial recursive program
that merely *eventually* emits the stage.  But the compiler already carries the stage table
as finite data — `enfPrefixFromTradeListsAtFuel` runs against an explicit
`D : ℕ → Finset Sentence`, instantiated at `decodedStageTable`, which is
`fun stages n => stages.getD n ∅` and so primitive recursive outright.  The source's own
Trading Firm reads stages exactly this way.  Letting the enforcer read them too costs
nothing and removes the hypothesis; refusing to would have been an artifact of this
interface rather than a fact about the mathematics.

An enforcer that does not need the stage simply ignores the argument. -/

/-- An enforcement trader presented as finite syntax: given the day, the day's deductive
stage and the ordinary aggregate's trades, it emits its own trades. -/
structure EffectiveEnforcer where
  /-- The day-`n` enforcement trades, as a function of the day's stage and the ordinary
  aggregate's trades. -/
  trades : ℕ → Finset Sentence → List (EF × Sentence) → List (EF × Sentence)
  /-- Every emitted coefficient is a legal day-`n` expressible feature. -/
  rank_le : ∀ (n : ℕ) (D : Finset Sentence) (ord : List (EF × Sentence))
    (p : EF × Sentence), p ∈ trades n D ord → p.1.rank ≤ n

/-- The day-`n` enforcement strategy against a given stage and ordinary aggregate. -/
def EffectiveEnforcer.strategy (E : EffectiveEnforcer) (n : ℕ) (D : Finset Sentence)
    (ord : Strategy n) : Strategy n where
  trades := E.trades n D ord.trades
  rank_le := fun p hp => E.rank_le n D ord.trades p hp

/-- The same enforcer as an `AdaptiveTrader`, so that every preservation theorem in
`DeductiveEnforcement` — all of which are generic in the added trader — applies to it
unchanged. -/
noncomputable def EffectiveEnforcer.adaptive (E : EffectiveEnforcer)
    (DP : DeductiveProcess) : AdaptiveTrader where
  action n past := E.strategy n (DP.D n) ((TradingFirm DP).action n past)

/-- The day-`n` aggregate built from a decoded stage table: the source firm's action
joined with the enforcer's. -/
def enfAggregateFromStages (D : ℕ → Finset Sentence) (E : EffectiveEnforcer)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) : Strategy n :=
  Strategy.join [TradingFirmAtFromStages D Q n,
    E.strategy n (D n) (TradingFirmAtFromStages D Q n)]

lemma enfAggregateFromStages_eq_aggregateAt (DP : DeductiveProcess)
    (E : EffectiveEnforcer) (D : ℕ → Finset Sentence)
    (past : List RationalBeliefState) (n : ℕ)
    (hD : ∀ m, m ≤ n → D m = DP.D m) :
    enfAggregateFromStages D E (rationalHistory past) n
      = aggregateAt DP (E.adaptive DP) n past := by
  unfold enfAggregateFromStages aggregateAt EffectiveEnforcer.adaptive
  rw [TradingFirmAtFromStages_eq_of_eq_prefix DP D _ n hD, hD n le_rfl]
  rfl

/-! ## The bounded recurrence -/

/-- Run `n` days of the modified recurrence from an explicit stage table, with one common
MarketMaker search bound. -/
def enfPrefixFromStagesAtFuel (D : ℕ → Finset Sentence) (E : EffectiveEnforcer)
    (fuel : ℕ) : ℕ → Option (List RationalBeliefState)
  | 0 => some []
  | n + 1 => do
      let past ← enfPrefixFromStagesAtFuel D E fuel n
      let state ← marketMakerSearchUpTo
        (enfAggregateFromStages D E (rationalHistory past) n) past
        (marketMakerError n) fuel
      some (past ++ [state])

/-- Canonical append-form prefix of the semantic modified states. -/
noncomputable def enfStatePrefix (DP : DeductiveProcess) (E : EffectiveEnforcer) :
    ℕ → List RationalBeliefState
  | 0 => []
  | n + 1 => enfStatePrefix DP E n ++ [states DP (E.adaptive DP) n]

@[simp] theorem enfStatePrefix_length (DP : DeductiveProcess) (E : EffectiveEnforcer)
    (n : ℕ) : (enfStatePrefix DP E n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [enfStatePrefix, ih]

lemma enfStatePrefix_getD (DP : DeductiveProcess) (E : EffectiveEnforcer) {n m : ℕ}
    (hm : m < n) :
    (enfStatePrefix DP E n).getD m (states DP (E.adaptive DP) 0)
      = states DP (E.adaptive DP) m := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [enfStatePrefix]
      by_cases hmn : m < n
      · rw [List.getD_append _ _ _ _ (by simpa using hmn)]
        exact ih hmn
      · have hmeq : m = n := by omega
        subst m
        simp [enfStatePrefix_length]

lemma enfStatePrefix_eq_ofFn (DP : DeductiveProcess) (E : EffectiveEnforcer) (n : ℕ) :
    enfStatePrefix DP E n = List.ofFn fun i : Fin n => states DP (E.adaptive DP) i := by
  apply List.ext_getElem
  · simp [enfStatePrefix_length]
  · intro i hi₁ hi₂
    simp only [List.getElem_ofFn]
    rw [← List.getD_eq_getElem (enfStatePrefix DP E n)
      (states DP (E.adaptive DP) 0) hi₁]
    apply enfStatePrefix_getD DP E
    simpa [enfStatePrefix_length] using hi₁

lemma enfPrefixFromStagesAtFuel_mono_success
    (D : ℕ → Finset Sentence) (E : EffectiveEnforcer) (n : ℕ)
    {fuel fuel' : ℕ} {states' : List RationalBeliefState}
    (hff : fuel ≤ fuel')
    (h : enfPrefixFromStagesAtFuel D E fuel n = some states') :
    enfPrefixFromStagesAtFuel D E fuel' n = some states' := by
  induction n generalizing states' with
  | zero => simpa [enfPrefixFromStagesAtFuel] using h
  | succ n ih =>
      simp only [enfPrefixFromStagesAtFuel] at h ⊢
      change Option.bind (enfPrefixFromStagesAtFuel D E fuel n)
        (fun past => Option.bind
          (marketMakerSearchUpTo
            (enfAggregateFromStages D E (rationalHistory past) n) past
            (marketMakerError n) fuel)
          (fun state => some (past ++ [state]))) = some states' at h
      change Option.bind (enfPrefixFromStagesAtFuel D E fuel' n)
        (fun past => Option.bind
          (marketMakerSearchUpTo
            (enfAggregateFromStages D E (rationalHistory past) n) past
            (marketMakerError n) fuel')
          (fun state => some (past ++ [state]))) = some states'
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨past, hpast, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨state, hstate, hout⟩ := h
      cases hout
      rw [ih hpast]
      simp only [Option.bind_some]
      rw [marketMakerSearchUpTo_mono_success _ _ _ hff hstate]
      rfl

lemma exists_enfPrefixFromStagesAtFuel
    (D : ℕ → Finset Sentence) (E : EffectiveEnforcer) (n : ℕ) :
    ∃ fuel states', enfPrefixFromStagesAtFuel D E fuel n = some states' := by
  induction n with
  | zero => exact ⟨0, [], rfl⟩
  | succ n ih =>
      obtain ⟨fuel₁, past, hpast⟩ := ih
      let T := enfAggregateFromStages D E (rationalHistory past) n
      let fuel₂ := marketMakerIndex T past (marketMakerError n)
        (marketMakerError_pos n) + 1
      let fuel := max fuel₁ fuel₂
      refine ⟨fuel, past ++ [MarketMaker T past (marketMakerError n)
        (marketMakerError_pos n)], ?_⟩
      simp only [enfPrefixFromStagesAtFuel]
      change Option.bind (enfPrefixFromStagesAtFuel D E fuel n)
        (fun prior => Option.bind
          (marketMakerSearchUpTo
            (enfAggregateFromStages D E (rationalHistory prior) n) prior
            (marketMakerError n) fuel)
          (fun state => some (prior ++ [state]))) = _
      rw [enfPrefixFromStagesAtFuel_mono_success D E n
        (Nat.le_max_left fuel₁ fuel₂) hpast]
      change Option.bind (marketMakerSearchUpTo T past (marketMakerError n) fuel)
        (fun state => some (past ++ [state])) = _
      rw [MarketMaker_search_of_clock_le T past (marketMakerError n)
        (marketMakerError_pos n) (Nat.le_max_right fuel₁ fuel₂)]
      rfl

/-- Every successful bounded run of the modified recurrence is the unique semantic
modified prefix. -/
lemma enfPrefixFromStagesAtFuel_sound (DP : DeductiveProcess) (E : EffectiveEnforcer)
    (D : ℕ → Finset Sentence) (fuel n : ℕ)
    (hD : ∀ m, m < n → D m = DP.D m)
    {states' : List RationalBeliefState}
    (h : enfPrefixFromStagesAtFuel D E fuel n = some states') :
    states' = enfStatePrefix DP E n := by
  induction n generalizing states' with
  | zero =>
      simp [enfPrefixFromStagesAtFuel] at h
      subst states'
      rfl
  | succ n ih =>
      simp only [enfPrefixFromStagesAtFuel] at h
      change Option.bind (enfPrefixFromStagesAtFuel D E fuel n)
        (fun past => Option.bind
          (marketMakerSearchUpTo
            (enfAggregateFromStages D E (rationalHistory past) n) past
            (marketMakerError n) fuel)
          (fun state => some (past ++ [state]))) = some states' at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨past, hpast, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨state, hstate, hout⟩ := h
      cases hout
      have hpastEq := ih (fun m hm => hD m (by omega)) hpast
      subst past
      have hagg := enfAggregateFromStages_eq_aggregateAt DP E D
        (enfStatePrefix DP E n) n (fun m hm => hD m (by omega))
      have hstateEq := MarketMaker_searchUpTo_sound
        (enfAggregateFromStages D E (rationalHistory (enfStatePrefix DP E n)) n)
        (enfStatePrefix DP E n) (marketMakerError n) (marketMakerError_pos n) hstate
      rw [hagg, enfStatePrefix_eq_ofFn] at hstateEq
      have hlia : state = states DP (E.adaptive DP) n := by
        rw [states]
        exact hstateEq
      rw [hlia]
      rfl

/-- One bounded end-to-end run: decode the required deductive stages, then execute the
modified recurrence with the same common bound. -/
def enfPrefixAtFuel {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (E : EffectiveEnforcer) (fuel n : ℕ) :
    Option (List RationalBeliefState) := do
  let stages ← processStagePrefixAtFuel process fuel n
  enfPrefixFromStagesAtFuel (decodedStageTable stages) E fuel n

lemma enfPrefixAtFuel_mono_success {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (E : EffectiveEnforcer) (n : ℕ)
    {fuel fuel' : ℕ} {states' : List RationalBeliefState}
    (hff : fuel ≤ fuel') (h : enfPrefixAtFuel process E fuel n = some states') :
    enfPrefixAtFuel process E fuel' n = some states' := by
  unfold enfPrefixAtFuel at h ⊢
  change Option.bind (processStagePrefixAtFuel process fuel n)
    (fun stages => enfPrefixFromStagesAtFuel (decodedStageTable stages) E fuel n) =
      some states' at h
  change Option.bind (processStagePrefixAtFuel process fuel' n)
    (fun stages => enfPrefixFromStagesAtFuel (decodedStageTable stages) E fuel' n) =
      some states'
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨stages, hstages, hstates⟩ := h
  rw [processStagePrefixAtFuel_mono_success process n hff hstages]
  exact enfPrefixFromStagesAtFuel_mono_success
    (decodedStageTable stages) E n hff hstates

lemma enfPrefixAtFuel_sound {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (E : EffectiveEnforcer) (fuel n : ℕ)
    {states' : List RationalBeliefState}
    (h : enfPrefixAtFuel process E fuel n = some states') :
    states' = enfStatePrefix DP E n := by
  unfold enfPrefixAtFuel at h
  change Option.bind (processStagePrefixAtFuel process fuel n)
    (fun stages => enfPrefixFromStagesAtFuel (decodedStageTable stages) E fuel n) =
      some states' at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨stages, hstages, hstates⟩ := h
  have hstageSound := processStagePrefixAtFuel_sound process fuel n hstages
  exact enfPrefixFromStagesAtFuel_sound DP E (decodedStageTable stages) fuel n
    hstageSound.2 hstates

lemma exists_enfPrefixAtFuel {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (E : EffectiveEnforcer) (n : ℕ) :
    ∃ fuel states', enfPrefixAtFuel process E fuel n = some states' := by
  obtain ⟨fuel₁, stages, hstages⟩ := exists_processStagePrefixAtFuel process n
  obtain ⟨fuel₂, states', hstates⟩ :=
    exists_enfPrefixFromStagesAtFuel (decodedStageTable stages) E n
  let fuel := max fuel₁ fuel₂
  refine ⟨fuel, states', ?_⟩
  unfold enfPrefixAtFuel
  change Option.bind (processStagePrefixAtFuel process fuel n)
    (fun decoded => enfPrefixFromStagesAtFuel (decodedStageTable decoded) E fuel n) =
      some states'
  rw [processStagePrefixAtFuel_mono_success process n
    (Nat.le_max_left fuel₁ fuel₂) hstages]
  exact enfPrefixFromStagesAtFuel_mono_success
    (decodedStageTable stages) E n (Nat.le_max_right fuel₁ fuel₂) hstates

/-! ## The exact rational quote -/

/-- Exact rational quote on arbitrary natural sentence codes; malformed codes are assigned
zero, as `ComputableMarket`'s total external table permits. -/
noncomputable def enfEncodedQuote (DP : DeductiveProcess) (E : EffectiveEnforcer)
    (day sentenceCode : ℕ) : ℚ :=
  match Encodable.decode (α := Sentence) sentenceCode with
  | some phi => quote DP (E.adaptive DP) day phi
  | none => 0

/-- Bounded exact quote evaluator for the modified market. -/
def enfEncodedQuoteAtFuel {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (E : EffectiveEnforcer)
    (fuel day sentenceCode : ℕ) : Option ℚ := do
  let states' ← enfPrefixAtFuel process E fuel (day + 1)
  let state ← states'[day]?
  some <| match Encodable.decode (α := Sentence) sentenceCode with
    | some phi => state.quote phi
    | none => 0

private lemma enfStatePrefix_getElem {DP : DeductiveProcess} (E : EffectiveEnforcer)
    (day : ℕ) (h : day < (enfStatePrefix DP E (day + 1)).length) :
    (enfStatePrefix DP E (day + 1))[day] = states DP (E.adaptive DP) day := by
  rw [← List.getD_eq_getElem (enfStatePrefix DP E (day + 1))
    (states DP (E.adaptive DP) 0) h]
  exact enfStatePrefix_getD DP E (by omega)

lemma enfEncodedQuoteAtFuel_sound {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (E : EffectiveEnforcer)
    {fuel day sentenceCode : ℕ} {q : ℚ}
    (h : enfEncodedQuoteAtFuel process E fuel day sentenceCode = some q) :
    q = enfEncodedQuote DP E day sentenceCode := by
  unfold enfEncodedQuoteAtFuel at h
  change Option.bind (enfPrefixAtFuel process E fuel (day + 1))
    (fun states' => Option.bind states'[day]? (fun state => some <|
      match Encodable.decode (α := Sentence) sentenceCode with
      | some phi => state.quote phi
      | none => 0)) = some q at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨states', hstates, h⟩ := h
  have hstatesEq := enfPrefixAtFuel_sound process E fuel (day + 1) hstates
  subst states'
  rw [enfStatePrefix_eq_ofFn] at h
  simp only [List.getElem?_ofFn] at h
  cases hdecode : Encodable.decode (α := Sentence) sentenceCode with
  | none => simpa [enfEncodedQuote, hdecode] using h.symm
  | some phi => simpa [enfEncodedQuote, quote, hdecode] using h.symm

lemma exists_enfEncodedQuoteAtFuel {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (E : EffectiveEnforcer)
    (day sentenceCode : ℕ) :
    ∃ fuel, enfEncodedQuoteAtFuel process E fuel day sentenceCode =
      some (enfEncodedQuote DP E day sentenceCode) := by
  obtain ⟨fuel, states', hstates⟩ := exists_enfPrefixAtFuel process E (day + 1)
  have hstatesEq := enfPrefixAtFuel_sound process E fuel (day + 1) hstates
  subst states'
  refine ⟨fuel, ?_⟩
  unfold enfEncodedQuoteAtFuel
  rw [hstates]
  change Option.bind (some (enfStatePrefix DP E (day + 1)))
    (fun states' => Option.bind states'[day]? (fun state => some <|
      match Encodable.decode (α := Sentence) sentenceCode with
      | some phi => state.quote phi
      | none => 0)) = some (enfEncodedQuote DP E day sentenceCode)
  simp only [Option.bind_some]
  have hday : day < (enfStatePrefix DP E (day + 1)).length := by
    simp [enfStatePrefix_length]
  rw [List.getElem?_eq_getElem hday, enfStatePrefix_getElem E day hday]
  cases hdecode : Encodable.decode (α := Sentence) sentenceCode with
  | none => simp [enfEncodedQuote, hdecode]
  | some phi => simp [enfEncodedQuote, quote, hdecode]

/-- Natural-coded bounded evaluator in the argument order `Partrec.rfindOpt` uses. -/
def enfEncodedQuoteNatAtFuel {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (E : EffectiveEnforcer)
    (z fuel : ℕ) : Option ℕ :=
  (enfEncodedQuoteAtFuel process E fuel z.unpair.1 z.unpair.2).map Encodable.encode

/-- **The one remaining compiler boundary for the modified market**, stated at exactly the
place the source states it for its own recurrence.  It carries no market correctness,
range, exploitation or logical-inductor content. -/
structure EnforcedBoundedEvaluatorCompiler {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (E : EffectiveEnforcer) where
  /-- The bounded evaluator is a computable two-argument natural function. -/
  computable : Computable₂ (enfEncodedQuoteNatAtFuel process E)

lemma enfEncodedQuoteNatAtFuel_sound {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (E : EffectiveEnforcer)
    {z fuel out : ℕ} (h : enfEncodedQuoteNatAtFuel process E z fuel = some out) :
    out = Encodable.encode (enfEncodedQuote DP E z.unpair.1 z.unpair.2) := by
  unfold enfEncodedQuoteNatAtFuel at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨q, hq, rfl⟩ := h
  rw [enfEncodedQuoteAtFuel_sound process E hq]

lemma exists_enfEncodedQuoteNatAtFuel {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (E : EffectiveEnforcer) (z : ℕ) :
    ∃ fuel, enfEncodedQuoteNatAtFuel process E z fuel =
      some (Encodable.encode (enfEncodedQuote DP E z.unpair.1 z.unpair.2)) := by
  obtain ⟨fuel, hfuel⟩ := exists_enfEncodedQuoteAtFuel process E z.unpair.1 z.unpair.2
  refine ⟨fuel, ?_⟩
  unfold enfEncodedQuoteNatAtFuel
  rw [hfuel]
  rfl

/-- Minimization over the fuel clock turns the compiler into one total partial-recursive
exact quote function. -/
lemma EnforcedBoundedEvaluatorCompiler.quote_computable
    {DP : DeductiveProcess} {process : DeductiveProcessComputation DP}
    {E : EffectiveEnforcer} (compiler : EnforcedBoundedEvaluatorCompiler process E) :
    Computable (fun z : ℕ =>
      Encodable.encode (enfEncodedQuote DP E z.unpair.1 z.unpair.2)) := by
  let search : ℕ → Part ℕ := fun z =>
    Nat.rfindOpt (enfEncodedQuoteNatAtFuel process E z)
  have hsearch : Partrec search := Partrec.rfindOpt compiler.computable
  apply hsearch.of_eq_tot
  intro z
  have hdom : (search z).Dom := by
    rw [Nat.rfindOpt_dom]
    obtain ⟨fuel, hfuel⟩ := exists_enfEncodedQuoteNatAtFuel process E z
    exact ⟨fuel, _, hfuel⟩
  let out := (search z).get hdom
  have hout : out ∈ search z := Part.get_mem hdom
  obtain ⟨fuel, hfuel⟩ := Nat.rfindOpt_spec hout
  have houtEq := enfEncodedQuoteNatAtFuel_sound process E hfuel
  rw [← houtEq]
  exact hout

lemma EnforcedBoundedEvaluatorCompiler.exists_quote_code
    {DP : DeductiveProcess} {process : DeductiveProcessComputation DP}
    {E : EffectiveEnforcer} (compiler : EnforcedBoundedEvaluatorCompiler process E) :
    ∃ code : Nat.Partrec.Code, ∀ z : ℕ,
      Encodable.encode (enfEncodedQuote DP E z.unpair.1 z.unpair.2) ∈ code.eval z := by
  have hcomp := compiler.quote_computable
  have hpart : Nat.Partrec (fun z : ℕ =>
      Part.some (Encodable.encode (enfEncodedQuote DP E z.unpair.1 z.unpair.2))) :=
    Partrec.nat_iff.mp hcomp.partrec
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp hpart
  refine ⟨code, ?_⟩
  intro z
  rw [hcode]
  simp

/-- **The modified market is computable.**  No `ComputableMarket` premise: the exact
rational quote program is exhibited. -/
theorem EnforcedBoundedEvaluatorCompiler.toComputableMarket
    {DP : DeductiveProcess} {process : DeductiveProcessComputation DP}
    {E : EffectiveEnforcer} (compiler : EnforcedBoundedEvaluatorCompiler process E) :
    ComputableMarket (history DP (E.adaptive DP)) := by
  obtain ⟨code, hcode⟩ := compiler.exists_quote_code
  refine ⟨fun n phi => history_range DP (E.adaptive DP) n phi,
    enfEncodedQuote DP E, code, ?_, hcode⟩
  intro n phi
  simp [history, enfEncodedQuote, quote, RationalBeliefState.toValuation]

/-! ## The criterion without a computability premise -/

/-- **Traderized deduction, with the market's own program supplied.**  The modified
deductive market is a logical inductor in the source's original sense, from a bounded
evaluator compiler and a per-date liability bound — no `ComputableMarket` hypothesis. -/
theorem isLogicalInductor_of_compiler {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (E : EffectiveEnforcer)
    (compiler : EnforcedBoundedEvaluatorCompiler process E) (B : ℝ)
    (hliab : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      -B ≤ (realizedEnforcer DP (E.adaptive DP)).netWorth
        (history DP (E.adaptive DP)) v n) :
    IsLogicalInductor (history DP (E.adaptive DP)) DP :=
  isLogicalInductor_of_computableMarket DP (E.adaptive DP) B process.toComputable
    hliab compiler.toComputableMarket

/-- The zero-risk-capital form: a per-date world-inclusive enforcer needs no bound at
all. -/
theorem isLogicalInductor_of_compiler_of_worldInclusive {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (E : EffectiveEnforcer)
    (compiler : EnforcedBoundedEvaluatorCompiler process E)
    (hday : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      0 ≤ ((realizedEnforcer DP (E.adaptive DP)).strat n).value
        (history DP (E.adaptive DP)) v.payout) :
    IsLogicalInductor (history DP (E.adaptive DP)) DP :=
  isLogicalInductor_of_compiler process E compiler 0
    (fun n v hv => by
      simpa using enforcement_netWorth_nonneg DP (E.adaptive DP) hday n v hv)

end Workspace.Normativity.Contrib.EnforcedComputation

#print axioms Workspace.Normativity.Contrib.EnforcedComputation.enfAggregateFromStages_eq_aggregateAt
#print axioms Workspace.Normativity.Contrib.EnforcedComputation.enfPrefixFromStagesAtFuel_sound
#print axioms Workspace.Normativity.Contrib.EnforcedComputation.enfPrefixAtFuel_sound
#print axioms Workspace.Normativity.Contrib.EnforcedComputation.exists_enfPrefixAtFuel
#print axioms Workspace.Normativity.Contrib.EnforcedComputation.enfEncodedQuoteAtFuel_sound
#print axioms Workspace.Normativity.Contrib.EnforcedComputation.EnforcedBoundedEvaluatorCompiler.quote_computable
#print axioms Workspace.Normativity.Contrib.EnforcedComputation.EnforcedBoundedEvaluatorCompiler.toComputableMarket
#print axioms Workspace.Normativity.Contrib.EnforcedComputation.isLogicalInductor_of_compiler
#print axioms Workspace.Normativity.Contrib.EnforcedComputation.isLogicalInductor_of_compiler_of_worldInclusive
