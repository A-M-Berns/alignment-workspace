import Cleanroom.Li.LiCoupledPair.A.Sealed
import Cleanroom.Li.LiCoupledPair.A.Sibling
import Cleanroom.Li.LiCoupledPair.A.JointInductor

/-!
# `li-coupled-pair` · A/SealedInductor: T4.2 (`contract_computable`) and T4.3
(`sealedSystem_of_uniform`) under `UniformLIAEvaluator`

The `A`-side recursion of `A/Sealed.lean` is computable under the package's one named hypothesis,
by the same route as `A/JointInductor.lean`: the step on the list of earlier days is computable
(`sealedStep_computable`) and reproduces the recursion (`sealedStep_spec`), so
`Computable.nat_strong_rec` gives `sealedDay_computable`, hence `A`'s table `aS` and the settled
values `Y` are computable, hence the three processes of record are `ComputableDeductiveProcess`
and FAF's `LIA_is_logical_inductor` supplies the three inductor fields of `SealedSiblingSystem`.

The new ingredient over `A/JointInductor.lean` is **running FAF's LIA over a process given by a
computable stage function, uniformly in a data parameter** (`liaStates_computable_param`): the
stage list `[D 0, …, D n]` is computable by a `Nat.rec` loop, and the day-`n` state is the total
evaluator's last entry on it (`liaStates_eq_prefixFromStages`). Applied to sibling `k`'s frozen
process at the table read off `A`'s past — whose stages are computable in `(past, k, s)`
(`siblingStage_computable_param`, the data-parametrized form of `A/Sibling.lean`'s
`siblingProcess_computable`) — it gives the contract value `sContract` as a computable function of
`(past, k)`, and T4.2's `contract_computable` as the fixed-table instance. This is where the
corpus's "computing `Y_n` costs about `R_H(F(n))`" lives: FAF has no cost, only computability.

Scope: **two-way.** Every theorem in this file that names `UniformLIAEvaluator` says so in
`Hyps:`, and its ledger row reads `partial: UniformLIAEvaluator (b)`; the unconditional
sibling-side facts and `sealedSystem_of_inductors` are here only because they need
`A/Sibling.lean` (which carries the compiler).
-/

namespace Cleanroom.Li.LiCoupledPair.A

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Cleanroom.Found.LiQuoteLane Cleanroom.Li.LiCoupledPair

/-! ## 1. FAF's LIA states of a computably-staged process, in a data parameter -/

/-- The `Nat.rec` accumulation of a function's values is its `List.range` map.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rec_concat_eq_map_range {α : Type} (g : ℕ → α) (m : ℕ) :
    (Nat.rec (motive := fun _ => List α) [] (fun y IH => IH ++ [g y]) m) =
      (List.range m).map g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show (Nat.rec (motive := fun _ => List α) [] (fun y IH => IH ++ [g y]) m) ++ [g m] = _
    rw [ih, List.range_succ, List.map_append]
    rfl

/-- The stage list `[D 0, …, D n]` of a stage function computable in a data parameter is
computable in `(data, n)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem stageList_computable_param {γ : Type} [Primcodable γ] {D : γ → ℕ → Finset Sentence}
    (hD : Computable fun p : γ × ℕ => D p.1 p.2) :
    Computable fun p : γ × ℕ => (List.range (p.2 + 1)).map (D p.1) := by
  have hh : Computable₂ fun (p : γ × ℕ) (q : ℕ × List (Finset Sentence)) =>
      q.2 ++ [D p.1 q.1] :=
    (Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      (hD.comp ((Computable.fst.comp Computable.fst).pair
        (Computable.fst.comp Computable.snd)))).of_eq fun _ => rfl
  refine (Computable.nat_rec (Primrec.succ.to_comp.comp Computable.snd) (Computable.const [])
    hh).of_eq fun p => ?_
  exact rec_concat_eq_map_range (D p.1) (p.2 + 1)

/-- FAF's day-`n` state is the total evaluator's last entry on the process's own stage list to
day `n` (`liaPrefixFromStages_eq` on the list `[D 0, …, D n]`, which decodes to `D` below
`n + 1`).
Source: none: infrastructure (FAF `liaPrefixFromStagesAtFuel_sound`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem liaStates_eq_prefixFromStages (DP : DeductiveProcess) (n : ℕ) :
    liaStates DP n =
      (liaPrefixFromStages ((List.range (n + 1)).map DP.D) (n + 1)).getD n emptyState := by
  rw [liaPrefixFromStages_eq DP _ (n + 1) ?_, getD_liaStatePrefix_succ]
  intro m hm
  unfold decodedStageTable
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp

/-- **Under `UniformLIAEvaluator`, FAF's LIA states of a process whose stages are computable in a
data parameter are computable in `(data, day)`.** The uniform evaluator run on the stage list.
Source: [[li-coupled-pair-mandate]] §Context (the uniform evaluator); mandate T4.2
Kind: C
Fidelity: exact
Hyps: (b) `UniformLIAEvaluator` (FAF private lemma, API request) -/
theorem liaStates_computable_param (hU : UniformLIAEvaluator) {γ : Type} [Primcodable γ]
    {DPf : γ → DeductiveProcess} (hD : Computable fun p : γ × ℕ => (DPf p.1).D p.2) :
    Computable fun p : γ × ℕ => liaStates (DPf p.1) p.2 := by
  have hev := liaPrefixFromStages_computable hU
  have hst : Computable fun p : γ × ℕ => (List.range (p.2 + 1)).map (DPf p.1).D :=
    stageList_computable_param (D := fun g s => (DPf g).D s) hD
  refine ((Primrec.list_getD emptyState).to_comp.comp
    (hev.comp (hst.pair (Primrec.succ.to_comp.comp Computable.snd))) Computable.snd : _).of_eq
    fun p => ?_
  exact (liaStates_eq_prefixFromStages (DPf p.1) p.2).symm

/-! ## 2. The frozen process's stages, computable in a data parameter -/

/-- A `filterMap` by `if p x then some x else none` is a `filter` by `p`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem filterMap_ite_eq_filter {α : Type} (p : α → Prop) [DecidablePred p] (l : List α) :
    l.filterMap (fun x => if p x then some x else none) = l.filter fun x => decide (p x) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases h : p x
    · simp [List.filterMap_cons, List.filter_cons, h, ih]
    · simp [List.filterMap_cons, List.filter_cons, h, ih]

/-- **The frozen process's stages are computable in a data parameter:** for a computable base, a
table computable in `(data, j, n)` and computable schedules,
`(siblingProcess base (a data) e N).D s` is computable in `((data, N), s)` — `A/Sibling.lean`'s
`siblingProcess_computable` with the table and the freezing day as data (the filter on
`entryDay < N` becomes a `filterMap` parametrized by `N`).
Source: mandate T4.2 ("the stage list of `siblingProcess … n` up to day `F n` is computable uniformly in `n`")
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem siblingStage_computable_param {β : Type} [Primcodable β] {base : DeductiveProcess}
    (hbase : ComputableDeductiveProcess base) {a : β → ℕ → ℕ → ℚ} {e : ℕ → PublicationSchedule}
    (ha : Computable fun z : β × ℕ × ℕ => a z.1 z.2.1 z.2.2)
    (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2) :
    Computable fun q : (β × ℕ) × ℕ => (siblingProcess base (a q.1.1) e q.1.2).D q.2 := by
  have hl : Computable fun q : (β × ℕ) × ℕ => recEntries (a q.1.1) e q.2 (candBound q.2) :=
    ((recEntries_computable_param ha he).comp
      ((Computable.fst.comp Computable.fst).pair Computable.snd) : _)
  have hpred : PrimrecPred fun w : (ℕ × List (ℕ × ℕ × Bool)) × (ℕ × ℕ × Bool) =>
      entryDay w.2 < w.1.1 :=
    Primrec.nat_lt.comp (entryDay_prim.comp Primrec.snd) (Primrec.fst.comp Primrec.fst)
  have hg : Primrec₂ fun (p : ℕ × List (ℕ × ℕ × Bool)) (x : ℕ × ℕ × Bool) =>
      if entryDay x < p.1 then some x else none :=
    (Primrec.ite hpred (Primrec.option_some.comp Primrec.snd) (Primrec.const none) : _)
  have hfm : Primrec fun p : ℕ × List (ℕ × ℕ × Bool) =>
      p.2.filterMap fun x => if entryDay x < p.1 then some x else none :=
    Primrec.listFilterMap Primrec.snd hg
  have hfilt : Computable fun q : (β × ℕ) × ℕ =>
      (recEntries (a q.1.1) e q.2 (candBound q.2)).filter fun x => decide (entryDay x < q.1.2) :=
    ((hfm.to_comp.comp ((Computable.snd.comp Computable.fst).pair hl)) : _).of_eq fun q =>
      filterMap_ite_eq_filter (fun x => entryDay x < q.1.2) _
  have hmap : Primrec fun l : List (ℕ × ℕ × Bool) => l.map literalOf :=
    Primrec.list_map Primrec.id (literalOf_prim.comp Primrec.snd).to₂
  have hlits : Computable fun q : (β × ℕ) × ℕ =>
      (((recEntries (a q.1.1) e q.2 (candBound q.2)).filter fun x =>
        decide (entryDay x < q.1.2)).map literalOf).toFinset :=
    sentenceList_toFinset_prim.to_comp.comp (hmap.to_comp.comp hfilt)
  have hbaseS : Computable fun q : (β × ℕ) × ℕ => base.D q.2 :=
    (stage_computable hbase).comp Computable.snd
  refine (sentenceFinset_union_prim.to_comp.comp hbaseS hlits).of_eq fun q => ?_
  rw [siblingProcess_D]
  congr 1
  ext φ
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_image, List.mem_filter,
    mem_recEntries_iff, mem_siblingEntries, decide_eq_true_eq]

/-- **Under `UniformLIAEvaluator`, the sibling's LIA states are computable in the table data, the
freezing day and the day.**
Source: mandate T4.2
Kind: C
Fidelity: exact
Hyps: (b) `UniformLIAEvaluator` -/
theorem siblingState_computable_param (hU : UniformLIAEvaluator) {β : Type} [Primcodable β]
    {base : DeductiveProcess} (hbase : ComputableDeductiveProcess base) {a : β → ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} (ha : Computable fun z : β × ℕ × ℕ => a z.1 z.2.1 z.2.2)
    (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2) :
    Computable fun q : (β × ℕ) × ℕ => liaStates (siblingProcess base (a q.1.1) e q.1.2) q.2 :=
  liaStates_computable_param hU (γ := β × ℕ) (DPf := fun g => siblingProcess base (a g.1) e g.2)
    (siblingStage_computable_param hbase ha he)

/-! ## 3. T4.2: the contract is computable -/

/-- **T4.2 (headline). `contract_computable`:** under `UniformLIAEvaluator`, for a computable base,
table and schedules, a computable horizon `F` and computable contract sentences `P`, the sealed
sibling's contract value `n ↦ H^{[n]}_{F n}(P n) = liaQuote (siblingProcess base a e n) (F n) (P n)`
is a computable function of `n`: sibling `n`'s stage list to day `F n` is computable uniformly in
`n` (`siblingStage_computable_param`), the uniform evaluator runs it, and the day-`F n` state's
quote of `P n` is read off. This is the corpus's "computing `Y_n` costs about `R_H(F(n))`"
(anson-016 §5): FAF has no cost, only computability — nothing is said about *how long* the run
takes. Scope: one-way per `n` (`A`'s table fixed); the two-way use is `sealedY_computable`.
Source: [[frozen-deliberation-deference-v6]] §5 (anson-016, the cost of `Y_n`); mandate T4.2
Kind: C
Fidelity: variant: computability, no cost model (li-quote-lane F8)
Hyps: (b) `UniformLIAEvaluator` (FAF private `liaPrefixFromStagesAtFuel_prim`; API request) -/
theorem contract_computable (hU : UniformLIAEvaluator) {base : DeductiveProcess}
    (hbase : ComputableDeductiveProcess base) {a : ℕ → ℕ → ℚ}
    (ha : Computable fun p : ℕ × ℕ => a p.1 p.2) {e : ℕ → PublicationSchedule}
    (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2) {F : ℕ → ℕ} (hF : Computable F)
    {P : ℕ → Sentence} (hP : Computable P) :
    Computable fun n => liaQuote (siblingProcess base a e n) (F n) (P n) := by
  have hst := siblingState_computable_param hU (β := Unit) (a := fun _ j n => a j n) hbase
    (ha.comp Computable.snd) he
  have hs : Computable fun n : ℕ => liaStates (siblingProcess base a e n) (F n) :=
    (hst.comp (((Computable.const ()).pair Computable.id).pair hF) : _)
  exact (rbs_quote_prim.to_comp.comp hs hP).of_eq fun _ => rfl

/-! ## 4. The computable step of the `A`-side recursion -/

/-- `A`'s table read off a state list is computable in `(list, j, n)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sTable_computable (S : SealedSpec) (hq : Computable fun p : ℕ × ℕ => S.quoted p.1 p.2) :
    Computable fun z : List RationalBeliefState × ℕ × ℕ => sTable S z.1 z.2.1 z.2.2 := by
  have hst : Computable fun z : List RationalBeliefState × ℕ × ℕ => z.1.getD z.2.2 emptyState :=
    (Primrec.list_getD emptyState).to_comp.comp Computable.fst (Computable.snd.comp Computable.snd)
  exact (rbs_quote_prim.to_comp.comp hst (hq.comp Computable.snd)).of_eq fun _ => rfl

/-- **The contract value read off `A`'s past is computable in `(past, k)`** under the hypothesis:
sibling `k` at the table read off the past, run to day `F k`, quoted at `contract k`.
Source: mandate T4.2/T4.3
Kind: C
Fidelity: exact
Hyps: (b) `UniformLIAEvaluator` -/
theorem sContract_computable (S : SealedSpec) (hU : UniformLIAEvaluator)
    (hbase : ComputableDeductiveProcess S.base)
    (hq : Computable fun p : ℕ × ℕ => S.quoted p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (S.e p.1).e p.2) (hc : Computable S.contract) :
    Computable fun z : List RationalBeliefState × ℕ × ℕ => sContract S z.1 z.2.2 := by
  have hst := siblingState_computable_param hU (β := List RationalBeliefState)
    (a := fun L j n => sTable S L j n) hbase (sTable_computable S hq) he
  have hk : Computable fun z : List RationalBeliefState × ℕ × ℕ => z.2.2 :=
    Computable.snd.comp Computable.snd
  have hs : Computable fun z : List RationalBeliefState × ℕ × ℕ =>
      liaStates (siblingProcess S.base (sTable S z.1) S.e z.2.2) (S.F.f z.2.2) :=
    (hst.comp ((Computable.fst.pair hk).pair (S.F.computable.comp hk)) : _)
  exact (rbs_quote_prim.to_comp.comp hs (hc.comp hk)).of_eq fun _ => rfl

/-- **`A`'s stage read off `A`'s past is computable in `(past, t)`** under the hypothesis
(`ledgerStage_computable_param` at the contract table).
Source: mandate T4.3
Kind: C
Fidelity: exact
Hyps: (b) `UniformLIAEvaluator` -/
theorem sStage_computable (S : SealedSpec) (hU : UniformLIAEvaluator)
    (hbase : ComputableDeductiveProcess S.base) (hA0 : ComputableDeductiveProcess S.DPA0)
    (hq : Computable fun p : ℕ × ℕ => S.quoted p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (S.e p.1).e p.2) (hc : Computable S.contract)
    (hσ : Computable S.σ.e) :
    Computable fun q : List RationalBeliefState × ℕ => sStage S q.1 q.2 :=
  ledgerStage_computable_param hA0 (a := fun L _ k => sContract S L k)
    (sContract_computable S hU hbase hq he hc) (hσ.comp Computable.snd)

/-- **The day step of the `A`-side recursion as a function of the earlier days** (the shape
`Computable.nat_strong_rec` consumes): from the list `L` of days `< t` (`t = L.length`), `A`'s
stage from `A`'s past states, then `A`'s state by the total evaluator on `A`'s stage list
extended by the new stage.
Source: mandate T4.3 (the recursion, in evaluator form)
Kind: D
Fidelity: n/a -/
noncomputable def sealedStep (S : SealedSpec) (L : List SealedDay) : Option SealedDay :=
  let t := L.length
  let past := L.map fun d => d.2
  let stages := L.map fun d => d.1
  let d := sStage S past t
  let s := (liaPrefixFromStages (stages ++ [d]) (t + 1)).getD t emptyState
  some (d, s)

/-- **The step is computable under the hypothesis.**
Source: mandate T4.3
Kind: C
Fidelity: exact
Hyps: (b) `UniformLIAEvaluator` -/
theorem sealedStep_computable (S : SealedSpec) (hU : UniformLIAEvaluator)
    (hbase : ComputableDeductiveProcess S.base) (hA0 : ComputableDeductiveProcess S.DPA0)
    (hq : Computable fun p : ℕ × ℕ => S.quoted p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (S.e p.1).e p.2) (hc : Computable S.contract)
    (hσ : Computable S.σ.e) :
    Computable (sealedStep S) := by
  have hstg := sStage_computable S hU hbase hA0 hq he hc hσ
  have hev := liaPrefixFromStages_computable hU
  have ht : Computable fun L : List SealedDay => L.length := Computable.list_length
  have hpast : Computable fun L : List SealedDay => L.map fun d => d.2 :=
    (Primrec.list_map Primrec.id (Primrec.snd.comp Primrec.snd).to₂).to_comp
  have hstages : Computable fun L : List SealedDay => L.map fun d => d.1 :=
    (Primrec.list_map Primrec.id (Primrec.fst.comp Primrec.snd).to₂).to_comp
  -- The `( … : _)` ascriptions are load-bearing (findings F8).
  have hd : Computable fun L : List SealedDay => sStage S (L.map fun d => d.2) L.length :=
    (hstg.comp (hpast.pair ht) : _)
  have hs : Computable fun L : List SealedDay =>
      (liaPrefixFromStages ((L.map fun d => d.1) ++ [sStage S (L.map fun d => d.2) L.length])
        (L.length + 1)).getD L.length emptyState :=
    ((Primrec.list_getD emptyState).to_comp.comp
      (hev.comp ((Computable.list_append.comp hstages
        (Computable.list_cons.comp hd (Computable.const []))).pair
        (Primrec.succ.to_comp.comp ht))) ht : _)
  exact (Computable.option_some.comp (hd.pair hs)).of_eq fun _ => rfl

/-- **The computable step reproduces the recursion:** on the list of days `< t` it returns
`some (sealedDay S t)` (the stage is the recursion's, `sealedDay_d`; the state is the total
evaluator's last entry on `A`'s stage list, which is `sealedDPA S`'s, hence
`liaStates (sealedDPA S) t`, hence the recursion's, `sealedDay_states`).
Source: mandate T4.3
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem sealedStep_spec (S : SealedSpec) (t : ℕ) :
    sealedStep S ((List.range t).map (sealedDay S)) = some (sealedDay S t) := by
  suffices key : ∀ L : List SealedDay, L = (List.range t).map (sealedDay S) →
      sealedStep S L = some (sealedDay S t) from key _ rfl
  intro L hL
  have hlen : L.length = t := by simp [hL]
  have hp : (L.map fun d => d.2) = sPast S t := by
    rw [hL, List.map_map, sPast, ofFn_eq_map_range (fun n => (sealedDay S n).2)]
    rfl
  have hlenS : (L.map fun d => d.1).length = t := by simp [hL]
  have htbl : ∀ m, m < t → (L.map fun d => d.1).getD m ∅ = (sealedDPA S).D m := by
    intro m hm
    rw [List.getD_eq_getElem _ _ (by simpa [hL] using hm)]
    simp [hL, sealedDay_d_eq]
  have e_d : sStage S (sPast S t) t = (sealedDay S t).1 := (sealedDay_d S t).symm
  have e_s : (liaPrefixFromStages ((L.map fun d => d.1) ++ [sStage S (sPast S t) t])
      (t + 1)).getD t emptyState = (sealedDay S t).2 := by
    rw [liaPrefixFromStages_eq (sealedDPA S) _ _
      (decodedStageTable_append hlenS htbl (by rw [e_d, sealedDay_d_eq])),
      getD_liaStatePrefix_succ, sealedDay_states S t]
  show some _ = _
  rw [hlen, hp, e_s, e_d]

/-! ## 5. The recursion, the tables and the processes are computable; the inductors -/

/-- **Under `UniformLIAEvaluator`, the `A`-side recursion is computable** (`Computable.nat_strong_rec`
on `sealedStep`).
Source: mandate T4.3
Kind: C
Fidelity: exact
Hyps: (b) `UniformLIAEvaluator` -/
theorem sealedDay_computable (S : SealedSpec) (hU : UniformLIAEvaluator)
    (hbase : ComputableDeductiveProcess S.base) (hA0 : ComputableDeductiveProcess S.DPA0)
    (hq : Computable fun p : ℕ × ℕ => S.quoted p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (S.e p.1).e p.2) (hc : Computable S.contract)
    (hσ : Computable S.σ.e) :
    Computable (sealedDay S) := by
  have h2 : Computable₂ fun (_ : Unit) (t : ℕ) => sealedDay S t :=
    Computable.nat_strong_rec (fun _ : Unit => sealedDay S) (g := fun _ L => sealedStep S L)
      ((sealedStep_computable S hU hbase hA0 hq he hc hσ).comp Computable.snd).to₂
      (fun _ n => sealedStep_spec S n)
  exact (h2.comp (Computable.const ()) Computable.id).of_eq fun _ => rfl

/-- **`A`'s table of record is computable** under the hypothesis.
Source: mandate T4.3
Kind: C
Fidelity: exact
Hyps: (b) `UniformLIAEvaluator` -/
theorem aS_computable (S : SealedSpec) (hU : UniformLIAEvaluator)
    (hbase : ComputableDeductiveProcess S.base) (hA0 : ComputableDeductiveProcess S.DPA0)
    (hq : Computable fun p : ℕ × ℕ => S.quoted p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (S.e p.1).e p.2) (hc : Computable S.contract)
    (hσ : Computable S.σ.e) :
    Computable fun p : ℕ × ℕ => aS S p.1 p.2 := by
  have hs : Computable fun p : ℕ × ℕ => (sealedDay S p.2).2 :=
    Computable.snd.comp ((sealedDay_computable S hU hbase hA0 hq he hc hσ).comp Computable.snd)
  exact (rbs_quote_prim.to_comp.comp hs hq).of_eq fun _ => rfl

/-- **T4.2 at the system: the settled values `Y` are computable** under the hypothesis
(`contract_computable` at the computable table of record).
Source: mandate T4.2/T4.3
Kind: C
Fidelity: variant: computability, no cost model
Hyps: (b) `UniformLIAEvaluator` -/
theorem sealedY_computable (S : SealedSpec) (hU : UniformLIAEvaluator)
    (hbase : ComputableDeductiveProcess S.base) (hA0 : ComputableDeductiveProcess S.DPA0)
    (hq : Computable fun p : ℕ × ℕ => S.quoted p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (S.e p.1).e p.2) (hc : Computable S.contract)
    (hσ : Computable S.σ.e) :
    Computable (sealedY S) :=
  (contract_computable hU hbase (aS_computable S hU hbase hA0 hq he hc hσ) he S.F.computable
    hc).of_eq fun _ => rfl

/-- **`A`'s process of record is a computable deductive process** under the hypothesis.
Source: mandate T4.3
Kind: C
Fidelity: exact
Hyps: (b) `UniformLIAEvaluator` -/
theorem sealedDPA_computable (S : SealedSpec) (hU : UniformLIAEvaluator)
    (hbase : ComputableDeductiveProcess S.base) (hA0 : ComputableDeductiveProcess S.DPA0)
    (hq : Computable fun p : ℕ × ℕ => S.quoted p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (S.e p.1).e p.2) (hc : Computable S.contract)
    (hσ : Computable S.σ.e) :
    ComputableDeductiveProcess (sealedDPA S) :=
  ledgerProcess_computable (a := fun _ n => sealedY S n) hA0
    ((sealedY_computable S hU hbase hA0 hq he hc hσ).comp Computable.snd) (hσ.comp Computable.snd)

/-- **`H⁺`'s process of record is a computable deductive process** under the hypothesis.
Source: mandate T4.3
Kind: C
Fidelity: exact
Hyps: (b) `UniformLIAEvaluator` -/
theorem sealedDPH_computable (S : SealedSpec) (hU : UniformLIAEvaluator)
    (hbase : ComputableDeductiveProcess S.base) (hA0 : ComputableDeductiveProcess S.DPA0)
    (hq : Computable fun p : ℕ × ℕ => S.quoted p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (S.e p.1).e p.2) (hc : Computable S.contract)
    (hσ : Computable S.σ.e) :
    ComputableDeductiveProcess (sealedDPH S) :=
  ledgerProcess_computable hbase (aS_computable S hU hbase hA0 hq he hc hσ) he

/-- **T4.3, `A`'s side: the market `A` of the sealed system is a logical inductor over its
process, which settles the contract to the siblings' quotes** — under `UniformLIAEvaluator`.
Source: [[frozen-deliberation-deference-v6]] §4 (anson-017); [[deference-in-logical-induction-v6]] §5.2 (root-deference-037); mandate T4.3
Kind: C
Fidelity: variant: plain trader class; exact rational contract
Hyps: (b) `UniformLIAEvaluator` (FAF private `liaPrefixFromStagesAtFuel_prim`; API request) -/
theorem sealedA_inductor (S : SealedSpec) (hU : UniformLIAEvaluator)
    (hbase : ComputableDeductiveProcess S.base) (hA0 : ComputableDeductiveProcess S.DPA0)
    (hq : Computable fun p : ℕ × ℕ => S.quoted p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (S.e p.1).e p.2) (hc : Computable S.contract)
    (hσ : Computable S.σ.e) :
    IsLogicalInductor (sealedA S) (sealedDPA S) := by
  unfold sealedA
  exact LIA_is_logical_inductor (sealedDPA S) (sealedDPA_computable S hU hbase hA0 hq he hc hσ)

/-- **T4.3, `H⁺`'s side: `H⁺` is a logical inductor over the full quote ledger of `A`** — under
`UniformLIAEvaluator` (only because `A`'s table is).
Source: mandate T4.3
Kind: C
Fidelity: variant: plain trader class
Hyps: (b) `UniformLIAEvaluator` -/
theorem sealedHplus_inductor (S : SealedSpec) (hU : UniformLIAEvaluator)
    (hbase : ComputableDeductiveProcess S.base) (hA0 : ComputableDeductiveProcess S.DPA0)
    (hq : Computable fun p : ℕ × ℕ => S.quoted p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (S.e p.1).e p.2) (hc : Computable S.contract)
    (hσ : Computable S.σ.e) :
    IsLogicalInductor (sealedHplus S) (sealedDPH S) := by
  unfold sealedHplus
  exact LIA_is_logical_inductor (sealedDPH S) (sealedDPH_computable S hU hbase hA0 hq he hc hσ)

/-- **T4.3, the family: every sealed sibling `H^{[N]}` is a logical inductor over its frozen
process at `A`'s table of record** — under `UniformLIAEvaluator` (only because `A`'s table is;
`sibling_inductor`'s argument).
Source: mandate T4.3; [[frozen-deliberation-deference-v6]] §3–§4 (anson-016/017)
Kind: C
Fidelity: variant: plain trader class
Hyps: (b) `UniformLIAEvaluator` -/
theorem sealedSib_inductor (S : SealedSpec) (hU : UniformLIAEvaluator)
    (hbase : ComputableDeductiveProcess S.base) (hA0 : ComputableDeductiveProcess S.DPA0)
    (hq : Computable fun p : ℕ × ℕ => S.quoted p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (S.e p.1).e p.2) (hc : Computable S.contract)
    (hσ : Computable S.σ.e) (N : ℕ) :
    IsLogicalInductor (sealedSib S N) (siblingProcess S.base (aS S) S.e N) :=
  LIA_is_logical_inductor _
    (siblingProcess_computable hbase (aS_computable S hU hbase hA0 hq he hc hσ) he N)

/-! ## 6. The sibling-side facts (unconditional) and the constructor -/

/-- **Every stage of every sibling's process has a consistent world**
(`SealedSiblingSystem.hworldSib`), for a base free of family `3` and satisfiable.
Source: mandate T4.3
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem sealed_hworldSib (S : SealedSpec) (hfree : ProcessFreeOf (ledgerSchedule (aS S) S.e) S.base)
    (h : ∀ n, ∃ v : PCWorld, v.ConsistentWith (S.base.D n)) (N : ℕ) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((siblingProcess S.base (aS S) S.e N).D n) :=
  sibling_hworld hfree h N

/-- **In sibling `N`, the ledger LUVs of days `n < N` are determined at `A`'s prices; nothing is
asserted for `n ≥ N`** (`SealedSiblingSystem.determinedSib`).
Source: mandate T4.3; [[frozen-deliberation-deference-v6]] §3 (anson-016)
Kind: C
Fidelity: exact (days `< N`; silent on `≥ N`)
Hyps: (a) none -/
theorem sealed_determinedSib (S : SealedSpec) (N j n : ℕ) (hN : n < N) :
    LUV.DeterminedVia (ledgerLuv j n) (siblingProcess S.base (aS S) S.e N) (aS S j n) :=
  siblingLuv_determinedVia S.base (aS S) S.e (aS_mem S) N j n hN

/-- **The sealed-sibling system, given the three inductor facts**: every other field of
`SealedSiblingSystem` is derived (`A/Sealed.lean` and above); the constructor takes only
`IsLogicalInductor` of `A`, `H⁺` and each sibling over the processes of record (what
`sealedSystem_of_uniform` supplies under `UniformLIAEvaluator`).
Source: mandate T4.3
Kind: C
Fidelity: variant: exact rational contract
Hyps: (a) none except the three inductor facts, which are the package's named-hypothesis rows -/
noncomputable def sealedSystem_of_inductors (S : SealedSpec)
    (hA : IsLogicalInductor (sealedA S) (sealedDPA S))
    (hH : IsLogicalInductor (sealedHplus S) (sealedDPH S))
    (hsib : ∀ N, IsLogicalInductor (sealedSib S N) (siblingProcess S.base (aS S) S.e N))
    (hfreeA : ProcessFreeOf (ledgerSchedule (fun _ n => sealedY S n) (fun _ => S.σ)) S.DPA0)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (S.DPA0.D n))
    (hfreeH : ProcessFreeOf (ledgerSchedule (aS S) S.e) S.base)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (S.base.D n)) : SealedSiblingSystem where
  base := S.base
  DPA0 := S.DPA0
  e := S.e
  F := S.F
  σ := S.σ
  e_lt_F := S.e_lt_F
  F_lt_σ := S.F_lt_σ
  quoted := S.quoted
  contract := S.contract
  a := aS S
  Y := sealedY S
  A := sealedA S
  Hplus := sealedHplus S
  sib := sealedSib S
  Y_eq := sealedY_eq S
  a_eq := sealed_a_eq S
  A_inductor := hA
  Hplus_inductor := hH
  sib_inductor := hsib
  hworldA := sealed_hworldA S hfreeA hworldA
  hworldH := sealed_hworldH S hfreeH hworldH
  hworldSib := fun N => sealed_hworldSib S hfreeH hworldH N
  determinedA := sealed_determinedA S
  determinedH := sealed_determinedH S
  determinedSib := sealed_determinedSib S

/-- **T4.3 (headline). The sealed-sibling system exists under `UniformLIAEvaluator`:** for
computable bases free of the ledger family and satisfiable, a computable quoted family and
contract enumeration, and computable schedules with publication before the horizon and settlement
after it, the `A`-side recursion yields a `SealedSiblingSystem` — `A` FAF's LIA over its base plus
the contract ledger settled to each sibling's **exact** day-`F n` quote, `H⁺` and every `H^{[N]}`
FAF's LIA over the base plus `A`'s (full, resp. frozen) quote ledger. No Brouwer step beyond FAF's
own; the one cost is the uniform evaluator. The unconditional form is OPEN (`sealedSystem_exists`).
Source: [[frozen-deliberation-deference-v6]] §3–§5 (anson-016/017); [[deference-in-logical-induction-v6]] §5.2 (root-deference-037); mandate T4.3
Kind: C
Fidelity: variant: exact rational contract (no grid rounding); plain trader class
Hyps: (b) `UniformLIAEvaluator` (FAF private `liaPrefixFromStagesAtFuel_prim`; API request) -/
noncomputable def sealedSystem_of_uniform (S : SealedSpec) (hU : UniformLIAEvaluator)
    (hbase : ComputableDeductiveProcess S.base) (hA0 : ComputableDeductiveProcess S.DPA0)
    (hq : Computable fun p : ℕ × ℕ => S.quoted p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (S.e p.1).e p.2) (hc : Computable S.contract)
    (hσ : Computable S.σ.e)
    (hfreeA : TagFreeProcess (cleanroomBaseTag + ledgerFamily) S.DPA0)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (S.DPA0.D n))
    (hfreeH : TagFreeProcess (cleanroomBaseTag + ledgerFamily) S.base)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (S.base.D n)) : SealedSiblingSystem :=
  sealedSystem_of_inductors S (sealedA_inductor S hU hbase hA0 hq he hc hσ)
    (sealedHplus_inductor S hU hbase hA0 hq he hc hσ)
    (sealedSib_inductor S hU hbase hA0 hq he hc hσ)
    (processFreeOf_ledgerSchedule_of_tagFree hfreeA) hworldA
    (processFreeOf_ledgerSchedule_of_tagFree hfreeH) hworldH

/-! ## 7. T4.3's witness: the system over the paper process -/

/-- **T4.3's witness spec:** both bases `paperDP 𝗜𝚺₁`; `A`'s prices of the day-varying atoms
`⟨0, ⟨j, n⟩⟩` published the **same day** into the `H`-side processes
(`PublicationSchedule.sameDay`); horizon `succDeferral` (sibling `n` is read at day `n + 1`);
settlement at `n + 2` (`payoutSchedule`); contract sentences the item-`0` atoms `⟨0, ⟨0, n⟩⟩`
(`A` quotes them, the siblings predict them). Same-day publication is forced by FAF's stock of
deferral functions: with next-day publication `e_lt_F` needs `F n > n + 1`, and FAF has
`succDeferral = n + 1` and `doublingDeferral = 2 ^ n` (which fails at `n = 0, 1`); an FP-certified
`n + 2` could be built, but is not needed — the sealed system has no `H`-side recursion, so
same-day reading is well-founded (`A`'s day-`n` state exists before any `H`-side process reads it).
**The channel is a variant of the source's** (repair round 1, audit r1 fidelity N3): in
[[frozen-deliberation-deference-v6]] §3 `A` "publishes a quote `a_n := A_n(C_n)`", its price of the
*contract* `C_n`, and that is what `H⁺` reads; here `H⁺` and the siblings read `A`'s prices of the
base propositions `⟨0, ⟨j, n⟩⟩` themselves, not of `C_n`. The source's channel
(`quoted j n := (ledgerLuv 0 n).gt (ratOfCode j)`, `A`'s day-`n` price of the contract's `j`-th
threshold sentence) is expressible in `SealedSpec`, but it puts `quoted` inside family 3, which
`H⁺`'s own ledger also uses (`Defs.lean`, `SealedSiblingSystem`'s disclosure (ii)); it is not
shipped. **`contract := witnessQuoted 0` is deliberate** (adversarial §3.8): the contract
`P^{(n)}` is `A`'s own item-`0` quoted atom of day `n`; sibling `n` is frozen at day `n`
(`siblingSchedule_mem_iff`), so it predicts the atom `A` quotes that day without seeing that quote.
Source: mandate T4.3 (`sealedSystem_exists`'s schedule clauses); [[frozen-deliberation-deference-v6]] §3 (`a_n := A_n(C_n)`)
Kind: D
Fidelity: variant: `A` quotes the base propositions `⟨0, ⟨j, n⟩⟩`, not the contract `C_n`; `contract = quoted 0` -/
noncomputable def paperSealedSpec : SealedSpec where
  base := paperDP 𝗜𝚺₁
  DPA0 := paperDP 𝗜𝚺₁
  e := fun _ => PublicationSchedule.sameDay
  F := succDeferral
  σ := payoutSchedule
  e_lt_F := fun _ n => by show n < n + 1; omega
  F_lt_σ := fun n => by show n + 1 < n + 2; omega
  quoted := witnessQuoted
  contract := witnessQuoted 0

/-- Same-day publication is computable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sameDaySchedule_computable :
    Computable fun p : ℕ × ℕ => ((fun _ : ℕ => PublicationSchedule.sameDay) p.1).e p.2 :=
  Computable.snd.of_eq fun _ => rfl

/-- The settlement schedule `n + 2` is computable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payoutSchedule_e_computable : Computable payoutSchedule.e :=
  (Primrec.succ.comp Primrec.succ).to_comp.of_eq fun _ => rfl

/-- **T4.3 (N+ for the conditional theorem): the sealed-sibling system over `paperDP 𝗜𝚺₁`, under
`UniformLIAEvaluator`.** Every other hypothesis of `sealedSystem_of_uniform` is discharged from
FAF's facts (`paperDP_computable`, `paperDP_cleanroomFree`, `paperDP_hworld`) and
`li-quote-lane`'s witnesses. A discharge of the hypothesis makes `sealedSystem_exists` `proved`
with no further work.
Source: mandate T4.3
Kind: N+
Fidelity: variant: exact rational contract; plain trader class
Hyps: (b) `UniformLIAEvaluator` -/
noncomputable def paperSealedSystem_of_uniform (hU : UniformLIAEvaluator) : SealedSiblingSystem :=
  sealedSystem_of_uniform paperSealedSpec hU (paperDP_computable 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁)
    witnessQuoted_computable sameDaySchedule_computable
    ((witnessQuoted_computable.comp ((Computable.const 0).pair Computable.id)).of_eq
      fun _ => rfl)
    payoutSchedule_e_computable
    ((paperDP_cleanroomFree 𝗜𝚺₁).tagFree (Nat.le_add_right _ _)) (paperDP_hworld 𝗜𝚺₁)
    ((paperDP_cleanroomFree 𝗜𝚺₁).tagFree (Nat.le_add_right _ _)) (paperDP_hworld 𝗜𝚺₁)

/-- **N+ grounds (unconditional): consecutive siblings' processes differ**, for any table in
`[0,1]` over a cleanroom-free base: the affirmed literal of item `0`, day `N`, threshold `-1` is
in a stage of `H^{[N+1]}`'s process and in no stage of `H^{[N]}`'s (`A/Sibling.lean`'s
`paperSiblingProcess_succ_ne`, with the table general).
Source: mandate T4.1/T4.3 N+ grounds
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem siblingProcess_succ_ne {base : DeductiveProcess} (hfree : CleanroomFreeProcess base)
    {a : ℕ → ℕ → ℚ} (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) (e : ℕ → PublicationSchedule) (N : ℕ) :
    siblingProcess base a e (N + 1) ≠ siblingProcess base a e N := by
  intro heq
  set j : ℕ := 0
  set s : ℕ := max (max N j) (max (Encodable.encode (-1 : ℚ)) ((e j).e N))
  have hmem' : (ledgerFamily, ledgerPayload j N (Encodable.encode (-1 : ℚ)), true) ∈
      (siblingSchedule a e (N + 1)).lits s := by
    rw [siblingSchedule_mem_iff]
    refine ⟨Nat.lt_succ_self N, le_max_of_le_left (le_max_left _ _),
      le_max_of_le_left (le_max_right _ _), le_max_of_le_right (le_max_left _ _),
      le_max_of_le_right (le_max_right _ _), ?_⟩
    have : (-1 : ℚ) < a j N := by linarith [(hmem j N).1]
    simp [this]
  have hin : freshAtom ledgerFamily (ledgerPayload j N (Encodable.encode (-1 : ℚ))) ∈
      (siblingProcess base a e (N + 1)).D s := by
    rw [siblingProcess_D, Finset.mem_union]
    exact Or.inr (Finset.mem_image.mpr ⟨_, by rw [← siblingSchedule_lits]; exact hmem', rfl⟩)
  rw [heq, siblingProcess_D, Finset.mem_union] at hin
  rcases hin with h | h
  · exact (hfree s _ h).freshAtomCode_notMem ledgerFamily
      (ledgerPayload j N (Encodable.encode (-1 : ℚ))) (by simp [freshAtom])
  · obtain ⟨x, hx, hx'⟩ := Finset.mem_image.mp h
    rw [← siblingSchedule_lits, mem_siblingSchedule_lits] at hx
    have hday : entryDay x = N := by
      obtain ⟨n', j', c', -, -, -, -, -, rfl⟩ :=
        mem_ledgerEntries.mp (List.mem_toFinset.mp (by rw [ledgerSchedule_lits] at hx; exact hx.1))
      rw [entryDay_ledgerEntry]
      simp only [ledgerEntry, literalOf] at hx'
      rcases hb : decide (ratOfCode c' < a j' n') with _ | _ <;> rw [hb] at hx' <;>
        simp only [Bool.cond_false, Bool.cond_true] at hx'
      · exact absurd hx' (by simp [freshAtom])
      · exact (ledgerPayload_inj.mp (freshAtom_inj.mp hx').2).1
    omega

/-- **N+ grounds (unconditional): in the paper witness, consecutive siblings' processes differ.**
Source: mandate T4.3 N+ grounds
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperSealed_sibling_succ_ne (N : ℕ) :
    siblingProcess paperSealedSpec.base (aS paperSealedSpec) paperSealedSpec.e (N + 1) ≠
      siblingProcess paperSealedSpec.base (aS paperSealedSpec) paperSealedSpec.e N :=
  siblingProcess_succ_ne (paperDP_cleanroomFree 𝗜𝚺₁) (aS_mem paperSealedSpec) _ N

/-- **N+ grounds (unconditional): `A`'s and `H⁺`'s processes differ.** At any stage `s` large
enough to carry the code of `-1`, `H⁺`'s process holds the affirmed quote literal of day `s`
(published the same day), while `A`'s process does not (its contract literals of day `s` settle at
`s + 2`, and `paperDP 𝗜𝚺₁` is cleanroom-free).
Source: mandate T4.3 N+ grounds (as T5.3's "the two jointly defined processes differ")
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperSealed_processes_differ (s : ℕ) (hs : Encodable.encode (-1 : ℚ) ≤ s) :
    (sealedDPH paperSealedSpec).D s ≠ (sealedDPA paperSealedSpec).D s := by
  intro heq
  set P := paperSealedSpec with hP
  have hmemH : (ledgerFamily, ledgerPayload 0 s (Encodable.encode (-1 : ℚ)), true) ∈
      (ledgerSchedule (aS P) P.e).lits s := by
    rw [ledgerSchedule_mem_iff]
    refine ⟨le_rfl, Nat.zero_le _, hs, ?_, ?_⟩
    · show s ≤ s
      exact le_rfl
    · have : (-1 : ℚ) < aS P 0 s := by linarith [(aS_mem P 0 s).1]
      simp [this]
  have hin : freshAtom ledgerFamily (ledgerPayload 0 s (Encodable.encode (-1 : ℚ))) ∈
      (sealedDPH P).D s := by
    unfold sealedDPH
    rw [ledgerProcess_D, Finset.mem_union]
    exact Or.inr (Finset.mem_image.mpr ⟨_, by rw [← ledgerSchedule_lits]; exact hmemH, rfl⟩)
  rw [heq] at hin
  unfold sealedDPA at hin
  rw [ledgerProcess_D, Finset.mem_union] at hin
  rcases hin with h | h
  · exact (paperDP_cleanroomFree 𝗜𝚺₁ s _ h).freshAtomCode_notMem ledgerFamily
      (ledgerPayload 0 s (Encodable.encode (-1 : ℚ))) (by simp [freshAtom])
  · obtain ⟨⟨f', p', b'⟩, hx, hx'⟩ := Finset.mem_image.mp h
    rw [← ledgerSchedule_lits] at hx
    cases b' with
    | false => exact absurd hx' (by simp [freshAtom])
    | true =>
      simp only [literalOf_true] at hx'
      obtain ⟨rfl, rfl⟩ := freshAtom_inj.mp hx'
      exact ledgerLuv_absent_before_payout (fun _ n => sealedY P n) (fun _ => P.σ) 0 s (-1 : ℚ) true
        (by show s < s + 2; omega) hx

/-- **N+ grounds (unconditional): both polarities occur in all three ledgers** — `A`'s contract
ledger, `H⁺`'s quote ledger, and every sibling's frozen ledger at days `n < N` (`r = -1` affirmed,
`r = 2` denied).
Source: mandate T4.3 N+ grounds
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperSealed_both_polarities (N j n : ℕ) (hN : n < N) :
    ((∃ s, (ledgerFamily, ledgerPayload 0 n (Encodable.encode (-1 : ℚ)), true) ∈
        (ledgerSchedule (fun _ n => sealedY paperSealedSpec n) (fun _ => paperSealedSpec.σ)).lits s) ∧
      ∃ s, (ledgerFamily, ledgerPayload 0 n (Encodable.encode (2 : ℚ)), false) ∈
        (ledgerSchedule (fun _ n => sealedY paperSealedSpec n) (fun _ => paperSealedSpec.σ)).lits s) ∧
    ((∃ s, (ledgerFamily, ledgerPayload j n (Encodable.encode (-1 : ℚ)), true) ∈
        (ledgerSchedule (aS paperSealedSpec) paperSealedSpec.e).lits s) ∧
      ∃ s, (ledgerFamily, ledgerPayload j n (Encodable.encode (2 : ℚ)), false) ∈
        (ledgerSchedule (aS paperSealedSpec) paperSealedSpec.e).lits s) ∧
    ((∃ s, (ledgerFamily, ledgerPayload j n (Encodable.encode (-1 : ℚ)), true) ∈
        (siblingSchedule (aS paperSealedSpec) paperSealedSpec.e N).lits s) ∧
      ∃ s, (ledgerFamily, ledgerPayload j n (Encodable.encode (2 : ℚ)), false) ∈
        (siblingSchedule (aS paperSealedSpec) paperSealedSpec.e N).lits s) := by
  refine ⟨ledgerSchedule_both_polarities _ _ (fun _ n => sealedY_mem paperSealedSpec n) 0 n,
    ledgerSchedule_both_polarities _ _ (aS_mem paperSealedSpec) j n, ?_⟩
  obtain ⟨⟨s₁, h₁⟩, ⟨s₂, h₂⟩⟩ :=
    ledgerSchedule_both_polarities (aS paperSealedSpec) paperSealedSpec.e (aS_mem paperSealedSpec) j n
  refine ⟨⟨s₁, ?_⟩, ⟨s₂, ?_⟩⟩
  · rw [mem_siblingSchedule_lits]
    exact ⟨h₁, by simp [entryDay, ledgerPayload, hN]⟩
  · rw [mem_siblingSchedule_lits]
    exact ⟨h₂, by simp [entryDay, ledgerPayload, hN]⟩

end Cleanroom.Li.LiCoupledPair.A
