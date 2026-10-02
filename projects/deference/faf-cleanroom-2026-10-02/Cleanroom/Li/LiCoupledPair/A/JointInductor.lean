import Cleanroom.Li.LiCoupledPair.DefsHeavy
import Cleanroom.Li.LiCoupledPair.A.Joint
import Cleanroom.Li.LiCoupledPair.A.LedgerDecided
import Cleanroom.Found.LiQuoteLane.Computability
import Cleanroom.Found.LiQuoteLane.Witnesses

/-!
# `li-coupled-pair` · A/JointInductor: the two-way pair under `UniformLIAEvaluator` (T5.1, T5.3)

`A/Joint.lean` builds the two processes of the two-way pair and identifies FAF's semantic LIA over
each with the staggered recursion `jointDay`; every `TwoWayPair` field but the two inductor facts
is derived there. The inductor facts need `ComputableDeductiveProcess` of the two processes
(`LIA_is_logical_inductor`), i.e. computability of the tables `aA`/`aH` of record, i.e. of the
recursion itself. This file proves that **under the package's one named hypothesis**
`UniformLIAEvaluator` (FAF's private `liaPrefixFromStagesAtFuel_prim`, graded (b)):

* `liaPrefixFromStages` is the *total* evaluator — the unique success of FAF's fuel-bounded
  `liaPrefixFromStagesAtFuel` on an explicit stage list (`exists_…` + `…_mono_success`) — and is
  computable in the stage list and the day given the hypothesis (`Nat.rfindOpt` on the fuel);
  its value is `liaStatePrefix DP n` for any `DP` agreeing with the list below `n`
  (`liaPrefixFromStages_eq`, FAF's `…_sound`).
* `jointStep` is the recursion's day step as a function of the list of earlier days
  (`Computable.nat_strong_rec`'s shape): `A`'s stage from `H`'s past states, `A`'s state by the
  total evaluator on `A`'s stage list, `H`'s stage from `A`'s states including the new one, `H`'s
  state likewise. It is computable (`jointStep_computable`: `li-quote-lane`'s ledger-stage
  enumeration parametrized by the state list, FAF's `Finset Sentence` encoding for `toFinset`
  and `∪`, `stateExpect` by the token-metered threshold codes of `XH`), and it reproduces the
  recursion (`jointStep_spec`: through `jointDay_dA_eq`/`dH_eq` and `jointDay_states`).
* Hence `jointDay` is computable (`jointDay_computable`), so are `aA` and `aH`, so are the two
  processes (`li-quote-lane` T1.4), so both markets are inductors (`jointA_inductor`,
  `jointH_inductor`), and **`twoWayPair_of_uniform : UniformLIAEvaluator → … → TwoWayPair`**.

**What this establishes about the sources.** [[deference-in-logical-induction-v6]] §5.2's "joint
existence is discharged, not assumed … the LI existence theorem applies to each process
separately" is right about the recursion (no Brouwer step beyond FAF's per-market one;
`A/Joint.lean`) and right about "applies to each process separately" **only given uniform
computability of FAF's evaluator in the stage table**, which FAF proves but keeps private. The
ledger rows read `partial: UniformLIAEvaluator (b)`; the unconditional form is the OPEN row
`twoWayPair_exists` (`li-coupled-pair-a-open.txt`). T5.3's witness `paperTwoWaySpec` (both bases
`paperDP 𝗜𝚺₁`, `cleanX`, `succDeferral`, `payoutSchedule`) instantiates the conditional theorem
(`paperTwoWayPair_of_uniform`) and carries the unconditional N+ grounds — the two jointly defined
processes differ (`paperTwoWay_processes_differ`) and both ledgers carry both polarities
(`paperTwoWay_both_polarities`) — so that a discharge of the hypothesis makes `twoWayPair_exists`
`proved` with no further work. Scope: **two-way, timed both ways.**
-/

namespace Cleanroom.Li.LiCoupledPair.A

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Cleanroom.Found.LiQuoteLane Cleanroom.Li.LiCoupledPair

/-! ## 1. The total evaluator, computable under the hypothesis -/

/-- **The total LIA state-prefix evaluator on an explicit stage list:** the unique success of FAF's
fuel-bounded `liaPrefixFromStagesAtFuel` (some fuel succeeds, `exists_liaPrefixFromStagesAtFuel`;
every success is the same list, `…_mono_success`/`…_sound`). Defined by choice; its computability
is `liaPrefixFromStages_computable` under `UniformLIAEvaluator`.
Source: none: infrastructure (FAF `liaPrefixFromStagesAtFuel`)
Kind: D
Fidelity: n/a -/
noncomputable def liaPrefixFromStages (stages : List (Finset Sentence)) (n : ℕ) :
    List RationalBeliefState :=
  (exists_liaPrefixFromStagesAtFuel (decodedStageTable stages) n).choose_spec.choose

/-- Some fuel evaluates to `liaPrefixFromStages`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem liaPrefixFromStages_spec (stages : List (Finset Sentence)) (n : ℕ) :
    ∃ fuel, liaPrefixFromStagesAtFuel (decodedStageTable stages) fuel n =
      some (liaPrefixFromStages stages n) :=
  ⟨_, (exists_liaPrefixFromStagesAtFuel (decodedStageTable stages) n).choose_spec.choose_spec⟩

/-- The total evaluator on a list agreeing with `DP` below `n` is `DP`'s semantic prefix (FAF's
`liaPrefixFromStagesAtFuel_sound`).
Source: none: infrastructure (FAF `liaPrefixFromStagesAtFuel_sound`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem liaPrefixFromStages_eq (DP : DeductiveProcess) (stages : List (Finset Sentence)) (n : ℕ)
    (hD : ∀ m, m < n → decodedStageTable stages m = DP.D m) :
    liaPrefixFromStages stages n = liaStatePrefix DP n := by
  obtain ⟨fuel, h⟩ := liaPrefixFromStages_spec stages n
  exact liaPrefixFromStagesAtFuel_sound DP _ fuel n hD h

/-- **Under `UniformLIAEvaluator`, the total evaluator is computable** in the stage list and the
day: `Nat.rfindOpt` on the fuel, total by `liaPrefixFromStages_spec`, monotone by FAF's
`…_mono_success`.
Source: [[li-coupled-pair-mandate]] §Context (the uniform evaluator); FAF `liaPrefixFromStagesAtFuel_mono_success`
Kind: C
Fidelity: exact
Hyps: (b) `UniformLIAEvaluator` (FAF private lemma, API request) -/
theorem liaPrefixFromStages_computable (hU : UniformLIAEvaluator) :
    Computable fun p : List (Finset Sentence) × ℕ => liaPrefixFromStages p.1 p.2 := by
  have hU' : Computable fun q : (List (Finset Sentence) × ℕ) × ℕ =>
      liaPrefixFromStagesAtFuel (decodedStageTable q.1.1) q.1.2 q.2 := hU
  have hf : Computable₂ fun (p : List (Finset Sentence) × ℕ) (fuel : ℕ) =>
      liaPrefixFromStagesAtFuel (decodedStageTable p.1) fuel p.2 :=
    (hU'.comp (((Computable.fst.comp Computable.fst).pair Computable.snd).pair
      (Computable.snd.comp Computable.fst))).of_eq fun _ => rfl
  refine (Partrec.rfindOpt hf).of_eq_tot fun p => ?_
  rw [Nat.rfindOpt_mono (fun {_ m n} hmn ha => Option.mem_def.mpr
    (liaPrefixFromStagesAtFuel_mono_success _ _ hmn (Option.mem_def.mp ha)))]
  obtain ⟨fuel, h⟩ := liaPrefixFromStages_spec p.1 p.2
  exact ⟨fuel, Option.mem_def.mpr h⟩

/-! ## 2. Primitive-recursive reads of states and finite stages -/

/-- The entry list of a belief state is primitive recursive (FAF's encoding erases the proof
fields).
Source: none: infrastructure (FAF `rationalBeliefStateEncodable`)
Kind: L
Fidelity: n/a -/
lemma rbs_entries_prim : Primrec RationalBeliefState.entries :=
  Primrec.encode_iff.mp
    ((Primrec.encode : Primrec fun B : RationalBeliefState => Encodable.encode B).of_eq
      fun _ => rfl)

/-- Association-list quotation is primitive recursive (FAF proves this privately; re-proved).
Source: none: infrastructure (FAF `quoteFromEntries_prim`, private)
Kind: L
Fidelity: n/a -/
lemma quoteFromEntries_prim' : Primrec₂ quoteFromEntries := by
  have hlookup : Primrec₂ fun (entries : List (Sentence × ℚ)) (φ : Sentence) =>
      entries.lookup φ := Primrec₂.swap Primrec.listLookup
  exact (Primrec.option_getD.comp₂ hlookup (Primrec₂.const 0)).of_eq fun entries φ => by
    induction entries with
    | nil => rfl
    | cons entry entries ih =>
        rcases entry with ⟨ψ, q⟩
        simp only [quoteFromEntries, List.lookup]
        split <;> simp_all

/-- Quoting a belief state is primitive recursive (FAF proves this privately; re-proved).
Source: none: infrastructure (FAF `rationalBeliefStateQuote_prim`, private)
Kind: L
Fidelity: n/a -/
lemma rbs_quote_prim : Primrec₂ RationalBeliefState.quote :=
  (quoteFromEntries_prim'.comp₂ (rbs_entries_prim.comp₂ Primrec₂.left) Primrec₂.right).of_eq
    fun _ _ => rfl

/-- `List.toFinset` on sentences is primitive recursive (FAF's canonical sorted encoding,
`encode_toFinset_eq`).
Source: none: infrastructure (FAF `encode_toFinset_eq`)
Kind: L
Fidelity: n/a -/
lemma sentenceList_toFinset_prim : Primrec fun l : List Sentence => l.toFinset :=
  Primrec.encode_iff.mp
    ((Primrec.encode.comp (sentenceInsertionSort_prim.comp dedup_prim)).of_eq
      fun l => (encode_toFinset_eq l).symm)

/-- Union of finite sentence sets is primitive recursive (FAF's `sentenceFinsetUnionNorm`).
Source: none: infrastructure (FAF `sentenceFinsetUnionNorm_spec`)
Kind: L
Fidelity: n/a -/
lemma sentenceFinset_union_prim : Primrec₂ fun s t : Finset Sentence => s ∪ t :=
  Primrec.encode_iff.mp
    ((sentenceFinsetUnionNorm_prim.comp (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst)
      (Primrec.encode.comp Primrec.snd))).of_eq fun p => sentenceFinsetUnionNorm_spec p.1 p.2)

/-! ## 3. Reading an expectation off a state is computable -/

/-- `stateExpect` is computable in the state, the LUV index and the day, from the family's e.c.
certificate (FAF's `expectQuoteAt_computable` with the state's `quote` in place of the program's).
Source: none: infrastructure (FAF `MarketComputation.expectQuoteAt_computable`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem stateExpect_computable {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X) :
    Computable fun z : RationalBeliefState × ℕ × ℕ => stateExpect z.1 (X z.2.1) z.2.2 := by
  have hcX : Primrec fun m : ℕ => Encodable.encode ((X m.unpair.1).gt
      ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ))) :=
    MachineSentenceCodes.primrec hX
  have hpack : Primrec fun w : (RationalBeliefState × ℕ × ℕ) × ℕ =>
      Nat.pair w.1.2.1 (Nat.pair (w.1.2.2 + 1) w.2) :=
    Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec₂.natPair.comp (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        Primrec.snd)
  have hgt : Primrec fun w : (RationalBeliefState × ℕ × ℕ) × ℕ =>
      Encodable.encode ((X w.1.2.1).gt ((w.2 : ℚ) / ((w.1.2.2 + 1 : ℕ) : ℚ))) :=
    (hcX.comp hpack).of_eq fun w => by simp [Nat.unpair_pair]
  have hsent : Primrec fun w : (RationalBeliefState × ℕ × ℕ) × ℕ =>
      (X w.1.2.1).gt ((w.2 : ℚ) / ((w.1.2.2 + 1 : ℕ) : ℚ)) :=
    Primrec.encode_iff.mp hgt
  have hcell : Primrec fun w : (RationalBeliefState × ℕ × ℕ) × ℕ =>
      w.1.1.quote ((X w.1.2.1).gt ((w.2 : ℚ) / ((w.1.2.2 + 1 : ℕ) : ℚ))) :=
    rbs_quote_prim.comp (Primrec.fst.comp Primrec.fst) hsent
  have hstep : Primrec₂ fun (z : RationalBeliefState × ℕ × ℕ) (p : ℕ × ℚ) =>
      p.2 + z.1.quote ((X z.2.1).gt ((p.1 : ℚ) / ((z.2.2 + 1 : ℕ) : ℚ))) :=
    (ratAdd_prim.comp (Primrec.snd.comp Primrec.snd)
      (hcell.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))).of_eq fun _ => rfl
  have hsum : Primrec fun z : RationalBeliefState × ℕ × ℕ =>
      ∑ i ∈ Finset.range (z.2.2 + 1), z.1.quote ((X z.2.1).gt ((i : ℚ) / ((z.2.2 + 1 : ℕ) : ℚ))) := by
    have hrec := Primrec.nat_rec' (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.const (0 : ℚ)) hstep
    refine hrec.of_eq fun z => ?_
    have key : ∀ m : ℕ, (Nat.rec (motive := fun _ => ℚ) 0
        (fun i s => s + z.1.quote ((X z.2.1).gt ((i : ℚ) / ((z.2.2 + 1 : ℕ) : ℚ)))) m) =
        ∑ i ∈ Finset.range m, z.1.quote ((X z.2.1).gt ((i : ℚ) / ((z.2.2 + 1 : ℕ) : ℚ))) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [Finset.sum_range_succ, ← ih]
    exact key (z.2.2 + 1)
  have hden : Primrec fun z : RationalBeliefState × ℕ × ℕ => ((z.2.2 + 1 : ℕ) : ℚ) :=
    ratNatCast_prim.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
  exact (ratDiv_prim.comp hsum hden).to_comp.of_eq fun _ => rfl

/-! ## 4. The ledger stage, computable in a data parameter -/

/-- `li-quote-lane`'s per-candidate entry list, computable when the table is computable in an
extra data parameter `β` (the parametrized `entryAt_computable`).
Source: none: infrastructure (`li-quote-lane` `entryAt_computable`)
Kind: L
Fidelity: n/a -/
theorem entryAt_computable_param {β : Type} [Primcodable β] {a : β → ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} (ha : Computable fun z : β × ℕ × ℕ => a z.1 z.2.1 z.2.2)
    (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2) :
    Computable fun q : β × ℕ × ℕ => entryAt (a q.1) e q.2.1 q.2.2 := by
  have hs : Primrec fun q : β × ℕ × ℕ => q.2.1 := Primrec.fst.comp Primrec.snd
  have hk : Primrec fun q : β × ℕ × ℕ => q.2.2 := Primrec.snd.comp Primrec.snd
  have hn : Primrec fun q : β × ℕ × ℕ => q.2.2.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hjc : Primrec fun q : β × ℕ × ℕ => q.2.2.unpair.2 := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hj : Primrec fun q : β × ℕ × ℕ => q.2.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hjc)
  have hc : Primrec fun q : β × ℕ × ℕ => q.2.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hjc)
  have hand : Primrec₂ (fun x y : Bool => x && y) := Primrec.dom_bool₂ _
  have hle1 : Primrec fun q : β × ℕ × ℕ => decide (q.2.2.unpair.1 ≤ q.2.1) :=
    Primrec.nat_le.decide.comp hn hs
  have hle2 : Primrec fun q : β × ℕ × ℕ => decide (q.2.2.unpair.2.unpair.1 ≤ q.2.1) :=
    Primrec.nat_le.decide.comp hj hs
  have hle3 : Primrec fun q : β × ℕ × ℕ => decide (q.2.2.unpair.2.unpair.2 ≤ q.2.1) :=
    Primrec.nat_le.decide.comp hc hs
  have hsome : Primrec fun q : β × ℕ × ℕ =>
      (Encodable.decode (α := ℚ) q.2.2.unpair.2.unpair.2).isSome :=
    Primrec.option_isSome.comp ((Primrec.decode (α := ℚ)).comp hc)
  have htest1 : Primrec fun q : β × ℕ × ℕ => decide (q.2.2.unpair.1 ≤ q.2.1) &&
      decide (q.2.2.unpair.2.unpair.1 ≤ q.2.1) && decide (q.2.2.unpair.2.unpair.2 ≤ q.2.1) &&
      (Encodable.decode (α := ℚ) q.2.2.unpair.2.unpair.2).isSome :=
    hand.comp (hand.comp (hand.comp hle1 hle2) hle3) hsome
  have htest2 : Computable fun q : β × ℕ × ℕ =>
      decide ((e q.2.2.unpair.2.unpair.1).e q.2.2.unpair.1 ≤ q.2.1) :=
    ((Primrec₂.to_comp Primrec.nat_le.decide).comp (he.comp (hj.to_comp.pair hn.to_comp))
      hs.to_comp : _)
  have htest : Computable fun q : β × ℕ × ℕ => entryTest e q.2.1 q.2.2 :=
    ((Primrec₂.to_comp hand).comp htest1.to_comp htest2).of_eq fun _ => rfl
  have hval : Computable fun q : β × ℕ × ℕ => a q.1 q.2.2.unpair.2.unpair.1 q.2.2.unpair.1 :=
    (ha.comp (Computable.fst.pair (hj.to_comp.pair hn.to_comp))).of_eq fun _ => rfl
  have hcode : Computable fun q : β × ℕ × ℕ => ratOfCode q.2.2.unpair.2.unpair.2 :=
    (ratOfCode_prim.comp hc).to_comp
  -- Rational `<` as a primitive recursive relation, from FAF's `ratLE_prim` at the `Prop` level
  -- (no `decide` in the unifier's way; the ascriptions below are load-bearing, as in FAF's
  -- `decodedQuotationRat_lt_computablePred`).
  have hltP : PrimrecRel fun p r : ℚ => p < r :=
    ((ratLE_prim.comp Primrec.snd Primrec.fst).not).of_eq fun z => by simp [not_le]
  have hltB : Primrec₂ fun p r : ℚ => decide (p < r) := hltP.decide
  have hpol : Computable fun q : β × ℕ × ℕ =>
      decide (ratOfCode q.2.2.unpair.2.unpair.2 < a q.1 q.2.2.unpair.2.unpair.1 q.2.2.unpair.1) :=
    ((Primrec₂.to_comp hltB).comp hcode hval : _)
  have hpay : Primrec fun q : β × ℕ × ℕ =>
      ledgerPayload q.2.2.unpair.2.unpair.1 q.2.2.unpair.1 q.2.2.unpair.2.unpair.2 :=
    (Primrec₂.natPair.comp hn (Primrec₂.natPair.comp hj hc)).of_eq fun _ => rfl
  have hentry : Computable fun q : β × ℕ × ℕ =>
      ledgerEntry (a q.1) q.2.2.unpair.2.unpair.1 q.2.2.unpair.1 q.2.2.unpair.2.unpair.2 :=
    ((Computable.const ledgerFamily).pair (hpay.to_comp.pair hpol)).of_eq fun _ => rfl
  exact (Computable.cond htest (Computable.list_cons.comp hentry (Computable.const []))
    (Computable.const [])).of_eq fun _ => rfl

/-- `li-quote-lane`'s recursive stage enumeration, computable in a data parameter.
Source: none: infrastructure (`li-quote-lane` `ledgerEntries_rec_computable`)
Kind: L
Fidelity: n/a -/
theorem recEntries_computable_param {β : Type} [Primcodable β] {a : β → ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} (ha : Computable fun z : β × ℕ × ℕ => a z.1 z.2.1 z.2.2)
    (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2) :
    Computable fun q : β × ℕ => recEntries (a q.1) e q.2 (candBound q.2) := by
  have h1 : Computable fun w : (β × ℕ) × (ℕ × List (ℕ × ℕ × Bool)) => w.2.2 :=
    Computable.snd.comp Computable.snd
  have h2 : Computable fun w : (β × ℕ) × (ℕ × List (ℕ × ℕ × Bool)) => (w.1.1, w.1.2, w.2.1) :=
    (Computable.fst.comp Computable.fst).pair
      ((Computable.snd.comp Computable.fst).pair (Computable.fst.comp Computable.snd))
  have h3 : Computable fun w : (β × ℕ) × (ℕ × List (ℕ × ℕ × Bool)) =>
      entryAt (a w.1.1) e w.1.2 w.2.1 :=
    ((entryAt_computable_param ha he).comp h2).of_eq fun _ => rfl
  have hh : Computable₂ fun (q : β × ℕ) (p : ℕ × List (ℕ × ℕ × Bool)) =>
      p.2 ++ entryAt (a q.1) e q.2 p.1 :=
    (Computable.list_append.comp h1 h3).of_eq fun _ => rfl
  refine (Computable.nat_rec (candBound_prim.to_comp.comp Computable.snd) (Computable.const [])
    hh).of_eq fun q => ?_
  rw [recEntries_eq_rec]

/-- Membership in `li-quote-lane`'s recursive enumeration is membership in the stage's entry list.
Source: none: infrastructure (`li-quote-lane` `recEntries_toFinset`)
Kind: L
Fidelity: n/a -/
lemma mem_recEntries_iff {a : ℕ → ℕ → ℚ} {e : ℕ → PublicationSchedule} {s : ℕ}
    {x : ℕ × ℕ × Bool} :
    x ∈ recEntries a e s (candBound s) ↔ x ∈ ledgerEntries a e s := by
  rw [← List.mem_toFinset, recEntries_toFinset, ledgerSchedule_lits, List.mem_toFinset]

/-- **The ledger stage is computable in a data parameter:** for a computable base, a table
computable in `(data, j, n)` and computable schedules, `(ledgerProcess base (a data) e).D s` is
computable in `(data, s)`.
Source: none: infrastructure (`li-quote-lane` T1.4, parametrized)
Kind: C
Fidelity: n/a
Hyps: (a) none -/
theorem ledgerStage_computable_param {β : Type} [Primcodable β] {base : DeductiveProcess}
    (hbase : ComputableDeductiveProcess base) {a : β → ℕ → ℕ → ℚ} {e : ℕ → PublicationSchedule}
    (ha : Computable fun z : β × ℕ × ℕ => a z.1 z.2.1 z.2.2)
    (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2) :
    Computable fun q : β × ℕ => (ledgerProcess base (a q.1) e).D q.2 := by
  have hl := recEntries_computable_param ha he
  have hmap : Primrec fun l : List (ℕ × ℕ × Bool) => l.map literalOf :=
    Primrec.list_map Primrec.id (literalOf_prim.comp Primrec.snd).to₂
  have hlits : Computable fun q : β × ℕ =>
      ((recEntries (a q.1) e q.2 (candBound q.2)).map literalOf).toFinset :=
    sentenceList_toFinset_prim.to_comp.comp (hmap.to_comp.comp hl)
  have hbaseS : Computable fun q : β × ℕ => base.D q.2 := (stage_computable hbase).comp Computable.snd
  refine (sentenceFinset_union_prim.to_comp.comp hbaseS hlits).of_eq fun q => ?_
  rw [ledgerProcess_D]
  congr 1
  ext φ
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_image, mem_recEntries_iff]

/-! ## 5. The computable step of the joint recursion -/

/-- **The day step of the joint recursion as a function of the earlier days** (the shape
`Computable.nat_strong_rec` consumes): from the list `L` of days `< t` (`t = L.length`), `A`'s
stage from `H`'s past states, `A`'s state by the total evaluator on `A`'s stage list extended by
the new stage, then `H`'s stage from `A`'s states including the new one, and `H`'s state.
Source: mandate T5.1 (the recursion, in evaluator form)
Kind: D
Fidelity: n/a -/
noncomputable def jointStep (P : TwoWaySpec) (L : List JointDay) : Option JointDay :=
  let t := L.length
  let pastA := L.map fun d => d.1.2
  let pastH := L.map fun d => d.2.2
  let stagesA := L.map fun d => d.1.1
  let stagesH := L.map fun d => d.2.1
  let dA := stageA P pastH t
  let sA := (liaPrefixFromStages (stagesA ++ [dA]) (t + 1)).getD t emptyState
  let dH := stageH P (pastA ++ [sA]) t
  let sH := (liaPrefixFromStages (stagesH ++ [dH]) (t + 1)).getD t emptyState
  some ((dA, sA), (dH, sH))

/-- **The step is computable under the hypothesis**, for computable bases, quoted family,
schedules and an e.c. `XH`.
Source: mandate T5.1
Kind: C
Fidelity: exact
Hyps: (b) `UniformLIAEvaluator` -/
theorem jointStep_computable (P : TwoWaySpec) (hU : UniformLIAEvaluator)
    (hA0 : ComputableDeductiveProcess P.DPA0) (hH0 : ComputableDeductiveProcess P.DPH0)
    (hq : Computable fun p : ℕ × ℕ => P.quotedA p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (P.e p.1).e p.2)
    (hX : LUV.MachineThresholdCodeSeq P.XH)
    (hσ : Computable fun p : ℕ × ℕ => (P.σ p.1).e p.2) :
    Computable (jointStep P) := by
  have htH : Computable fun z : List RationalBeliefState × ℕ × ℕ => tableH P z.1 z.2.1 z.2.2 := by
    have hday : Computable fun z : List RationalBeliefState × ℕ × ℕ => P.f.f z.2.2 :=
      P.f.computable.comp (Computable.snd.comp Computable.snd)
    have hst : Computable fun z : List RationalBeliefState × ℕ × ℕ =>
        z.1.getD (P.f.f z.2.2) emptyState :=
      (Primrec.list_getD emptyState).to_comp.comp Computable.fst hday
    exact ((stateExpect_computable hX).comp
      (hst.pair ((Computable.snd.comp Computable.snd).pair hday))).of_eq fun _ => rfl
  have htA : Computable fun z : List RationalBeliefState × ℕ × ℕ => tableA P z.1 z.2.1 z.2.2 := by
    have hst : Computable fun z : List RationalBeliefState × ℕ × ℕ => z.1.getD z.2.2 emptyState :=
      (Primrec.list_getD emptyState).to_comp.comp Computable.fst (Computable.snd.comp Computable.snd)
    exact (rbs_quote_prim.to_comp.comp hst (hq.comp Computable.snd)).of_eq fun _ => rfl
  have hstA : Computable fun q : List RationalBeliefState × ℕ => stageA P q.1 q.2 :=
    ledgerStage_computable_param hA0 (a := fun L j n => tableH P L j n) htH hσ
  have hstH : Computable fun q : List RationalBeliefState × ℕ => stageH P q.1 q.2 :=
    ledgerStage_computable_param hH0 (a := fun L j n => tableA P L j n) htA he
  have hev := liaPrefixFromStages_computable hU
  have ht : Computable fun L : List JointDay => L.length := Computable.list_length
  have hpastA : Computable fun L : List JointDay => L.map fun d => d.1.2 :=
    (Primrec.list_map Primrec.id ((Primrec.snd.comp Primrec.fst).comp Primrec.snd).to₂).to_comp
  have hpastH : Computable fun L : List JointDay => L.map fun d => d.2.2 :=
    (Primrec.list_map Primrec.id ((Primrec.snd.comp Primrec.snd).comp Primrec.snd).to₂).to_comp
  have hstagesA : Computable fun L : List JointDay => L.map fun d => d.1.1 :=
    (Primrec.list_map Primrec.id ((Primrec.fst.comp Primrec.fst).comp Primrec.snd).to₂).to_comp
  have hstagesH : Computable fun L : List JointDay => L.map fun d => d.2.1 :=
    (Primrec.list_map Primrec.id ((Primrec.fst.comp Primrec.snd).comp Primrec.snd).to₂).to_comp
  -- The `( … : _)` ascriptions below are load-bearing: they force bottom-up elaboration, so the
  -- unifier never tries to split `?f (?g L)` against the compound heads `stageA`/`getD`.
  have hdA : Computable fun L : List JointDay => stageA P (L.map fun d => d.2.2) L.length :=
    (hstA.comp (hpastH.pair ht) : _)
  have hsA : Computable fun L : List JointDay =>
      (liaPrefixFromStages ((L.map fun d => d.1.1) ++ [stageA P (L.map fun d => d.2.2) L.length])
        (L.length + 1)).getD L.length emptyState :=
    ((Primrec.list_getD emptyState).to_comp.comp
      (hev.comp ((Computable.list_append.comp hstagesA
        (Computable.list_cons.comp hdA (Computable.const []))).pair
        (Primrec.succ.to_comp.comp ht))) ht : _)
  have hdH : Computable fun L : List JointDay => stageH P ((L.map fun d => d.1.2) ++
      [(liaPrefixFromStages ((L.map fun d => d.1.1) ++
        [stageA P (L.map fun d => d.2.2) L.length]) (L.length + 1)).getD L.length emptyState])
      L.length :=
    (hstH.comp ((Computable.list_append.comp hpastA
      (Computable.list_cons.comp hsA (Computable.const []))).pair ht) : _)
  have hsH : Computable fun L : List JointDay =>
      (liaPrefixFromStages ((L.map fun d => d.2.1) ++ [stageH P ((L.map fun d => d.1.2) ++
        [(liaPrefixFromStages ((L.map fun d => d.1.1) ++
          [stageA P (L.map fun d => d.2.2) L.length]) (L.length + 1)).getD L.length emptyState])
        L.length]) (L.length + 1)).getD L.length emptyState :=
    ((Primrec.list_getD emptyState).to_comp.comp
      (hev.comp ((Computable.list_append.comp hstagesH
        (Computable.list_cons.comp hdH (Computable.const []))).pair
        (Primrec.succ.to_comp.comp ht))) ht : _)
  exact (Computable.option_some.comp ((hdA.pair hsA).pair (hdH.pair hsH))).of_eq fun _ => rfl

/-! ## 6. The step reproduces the recursion -/

/-- `List.ofFn` over `Fin t` is `List.map` over `List.range t`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ofFn_eq_map_range {α : Type} (g : ℕ → α) (t : ℕ) :
    (List.ofFn fun i : Fin t => g i) = (List.range t).map g := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_ofFn]

/-- The last entry of the semantic prefix to day `t + 1` is the day-`t` state, for any default.
Source: none: infrastructure (FAF `liaStatePrefix_getD`)
Kind: L
Fidelity: n/a -/
lemma getD_liaStatePrefix_succ (DP : DeductiveProcess) (t : ℕ) (d : RationalBeliefState) :
    (liaStatePrefix DP (t + 1)).getD t d = liaStates DP t := by
  have hlen : t < (liaStatePrefix DP (t + 1)).length := by
    rw [liaStatePrefix_length]
    omega
  rw [List.getD_eq_getElem _ _ hlen, ← List.getD_eq_getElem _ (liaStates DP 0) hlen,
    liaStatePrefix_getD DP (Nat.lt_succ_self t)]

/-- A stage list agreeing with `D` below `t`, extended by `D t`, decodes to `D` below `t + 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma decodedStageTable_append {stages : List (Finset Sentence)} {d : Finset Sentence}
    {D : ℕ → Finset Sentence} {t : ℕ} (hlen : stages.length = t)
    (hs : ∀ m, m < t → stages.getD m ∅ = D m) (hd : d = D t) :
    ∀ m, m < t + 1 → decodedStageTable (stages ++ [d]) m = D m := by
  intro m hm
  unfold decodedStageTable
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hm) with h | rfl
  · rw [List.getD_append _ _ _ _ (by omega)]
    exact hs m h
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hlen, hd]

/-- **The computable step reproduces the recursion:** on the list of days `< t` it returns
`some (jointDay P t)`. The `A`-stage is the recursion's (`jointDay_dA`); the `A`-state is the total
evaluator's last entry on `A`'s stage list (which is `jointDPA P`'s, `jointDay_dA_eq`), hence
`liaStates (jointDPA P) t` (`liaPrefixFromStages_eq`), hence the recursion's (`jointDay_states`);
likewise for `H`.
Source: mandate T5.1
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem jointStep_spec (P : TwoWaySpec) (t : ℕ) :
    jointStep P ((List.range t).map (jointDay P)) = some (jointDay P t) := by
  suffices key : ∀ L : List JointDay, L = (List.range t).map (jointDay P) →
      jointStep P L = some (jointDay P t) from key _ rfl
  intro L hL
  have hlen : L.length = t := by simp [hL]
  have hpA : (L.map fun d => d.1.2) = pastA P t := by
    rw [hL, List.map_map, pastA, ofFn_eq_map_range (fun n => (jointDay P n).1.2)]
    rfl
  have hpH : (L.map fun d => d.2.2) = pastH P t := by
    rw [hL, List.map_map, pastH, ofFn_eq_map_range (fun n => (jointDay P n).2.2)]
    rfl
  have hlenA : (L.map fun d => d.1.1).length = t := by simp [hL]
  have hlenH : (L.map fun d => d.2.1).length = t := by simp [hL]
  have hsA_tbl : ∀ m, m < t → (L.map fun d => d.1.1).getD m ∅ = (jointDPA P).D m := by
    intro m hm
    rw [List.getD_eq_getElem _ _ (by simpa [hL] using hm)]
    simp [hL, jointDay_dA_eq]
  have hsH_tbl : ∀ m, m < t → (L.map fun d => d.2.1).getD m ∅ = (jointDPH P).D m := by
    intro m hm
    rw [List.getD_eq_getElem _ _ (by simpa [hL] using hm)]
    simp [hL, jointDay_dH_eq]
  have e_dA : stageA P (pastH P t) t = (jointDay P t).1.1 := (jointDay_dA P t).symm
  have e_sA : (liaPrefixFromStages ((L.map fun d => d.1.1) ++ [stageA P (pastH P t) t])
      (t + 1)).getD t emptyState = (jointDay P t).1.2 := by
    rw [liaPrefixFromStages_eq (jointDPA P) _ _
      (decodedStageTable_append hlenA hsA_tbl (by rw [e_dA, jointDay_dA_eq])),
      getD_liaStatePrefix_succ, (jointDay_states P t).1]
  have e_dH : stageH P (pastA P t ++ [(jointDay P t).1.2]) t = (jointDay P t).2.1 :=
    (jointDay_dH P t).symm
  have e_sH : (liaPrefixFromStages ((L.map fun d => d.2.1) ++
      [stageH P (pastA P t ++ [(jointDay P t).1.2]) t]) (t + 1)).getD t emptyState =
      (jointDay P t).2.2 := by
    rw [liaPrefixFromStages_eq (jointDPH P) _ _
      (decodedStageTable_append hlenH hsH_tbl (by rw [e_dH, jointDay_dH_eq])),
      getD_liaStatePrefix_succ, (jointDay_states P t).2]
  show some _ = _
  rw [hlen, hpA, hpH, e_sA, e_dA, e_sH, e_dH]

/-! ## 7. The recursion is computable; the inductors; the pair -/

/-- **Under `UniformLIAEvaluator`, the joint recursion is computable** (`Computable.nat_strong_rec`
on `jointStep`).
Source: mandate T5.1
Kind: C
Fidelity: exact
Hyps: (b) `UniformLIAEvaluator` -/
theorem jointDay_computable (P : TwoWaySpec) (hU : UniformLIAEvaluator)
    (hA0 : ComputableDeductiveProcess P.DPA0) (hH0 : ComputableDeductiveProcess P.DPH0)
    (hq : Computable fun p : ℕ × ℕ => P.quotedA p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (P.e p.1).e p.2)
    (hX : LUV.MachineThresholdCodeSeq P.XH)
    (hσ : Computable fun p : ℕ × ℕ => (P.σ p.1).e p.2) :
    Computable (jointDay P) := by
  have h2 : Computable₂ fun (_ : Unit) (t : ℕ) => jointDay P t :=
    Computable.nat_strong_rec (fun _ : Unit => jointDay P) (g := fun _ L => jointStep P L)
      ((jointStep_computable P hU hA0 hH0 hq he hX hσ).comp Computable.snd).to₂
      (fun _ n => jointStep_spec P n)
  exact (h2.comp (Computable.const ()) Computable.id).of_eq fun _ => rfl

/-- **`A`'s table of record is computable** under the hypothesis.
Source: mandate T5.1
Kind: C
Fidelity: exact
Hyps: (b) `UniformLIAEvaluator` -/
theorem aA_computable (P : TwoWaySpec) (hU : UniformLIAEvaluator)
    (hA0 : ComputableDeductiveProcess P.DPA0) (hH0 : ComputableDeductiveProcess P.DPH0)
    (hq : Computable fun p : ℕ × ℕ => P.quotedA p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (P.e p.1).e p.2)
    (hX : LUV.MachineThresholdCodeSeq P.XH)
    (hσ : Computable fun p : ℕ × ℕ => (P.σ p.1).e p.2) :
    Computable fun p : ℕ × ℕ => aA P p.1 p.2 := by
  have hs : Computable fun p : ℕ × ℕ => (jointDay P p.2).1.2 :=
    Computable.snd.comp (Computable.fst.comp
      ((jointDay_computable P hU hA0 hH0 hq he hX hσ).comp Computable.snd))
  exact (rbs_quote_prim.to_comp.comp hs hq).of_eq fun _ => rfl

/-- **`H`'s table of record is computable** under the hypothesis.
Source: mandate T5.1
Kind: C
Fidelity: exact
Hyps: (b) `UniformLIAEvaluator` -/
theorem aH_computable (P : TwoWaySpec) (hU : UniformLIAEvaluator)
    (hA0 : ComputableDeductiveProcess P.DPA0) (hH0 : ComputableDeductiveProcess P.DPH0)
    (hq : Computable fun p : ℕ × ℕ => P.quotedA p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (P.e p.1).e p.2)
    (hX : LUV.MachineThresholdCodeSeq P.XH)
    (hσ : Computable fun p : ℕ × ℕ => (P.σ p.1).e p.2) :
    Computable fun p : ℕ × ℕ => aH P p.1 p.2 := by
  have hday : Computable fun p : ℕ × ℕ => P.f.f p.2 := P.f.computable.comp Computable.snd
  have hs : Computable fun p : ℕ × ℕ => (jointDay P (P.f.f p.2)).2.2 :=
    Computable.snd.comp (Computable.snd.comp
      ((jointDay_computable P hU hA0 hH0 hq he hX hσ).comp hday))
  exact ((stateExpect_computable hX).comp (hs.pair (Computable.snd.pair hday))).of_eq
    fun _ => rfl

/-- **`A`'s process of record is a computable deductive process** under the hypothesis.
Source: mandate T5.1
Kind: C
Fidelity: exact
Hyps: (b) `UniformLIAEvaluator` -/
theorem jointDPA_computable (P : TwoWaySpec) (hU : UniformLIAEvaluator)
    (hA0 : ComputableDeductiveProcess P.DPA0) (hH0 : ComputableDeductiveProcess P.DPH0)
    (hq : Computable fun p : ℕ × ℕ => P.quotedA p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (P.e p.1).e p.2)
    (hX : LUV.MachineThresholdCodeSeq P.XH)
    (hσ : Computable fun p : ℕ × ℕ => (P.σ p.1).e p.2) :
    ComputableDeductiveProcess (jointDPA P) :=
  ledgerProcess_computable (a := aH P) hA0 (aH_computable P hU hA0 hH0 hq he hX hσ) hσ

/-- **`H`'s process of record is a computable deductive process** under the hypothesis.
Source: mandate T5.1
Kind: C
Fidelity: exact
Hyps: (b) `UniformLIAEvaluator` -/
theorem jointDPH_computable (P : TwoWaySpec) (hU : UniformLIAEvaluator)
    (hA0 : ComputableDeductiveProcess P.DPA0) (hH0 : ComputableDeductiveProcess P.DPH0)
    (hq : Computable fun p : ℕ × ℕ => P.quotedA p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (P.e p.1).e p.2)
    (hX : LUV.MachineThresholdCodeSeq P.XH)
    (hσ : Computable fun p : ℕ × ℕ => (P.σ p.1).e p.2) :
    ComputableDeductiveProcess (jointDPH P) :=
  ledgerProcess_computable (a := aA P) hH0 (aA_computable P hU hA0 hH0 hq he hX hσ) he

/-- **T5.1, `A`'s side: the market `A` of the two-way pair is a logical inductor over its process,
which reads `H`** — under `UniformLIAEvaluator`.
Source: mandate T5.1; [[deference-in-logical-induction-v6]] §5.2 (root-deference-037); [[route-sparse-schedule]] §9 (vq-wiki-067)
Kind: C
Fidelity: variant: plain trader class
Hyps: (b) `UniformLIAEvaluator` (FAF private `liaPrefixFromStagesAtFuel_prim`; API request) -/
theorem jointA_inductor (P : TwoWaySpec) (hU : UniformLIAEvaluator)
    (hA0 : ComputableDeductiveProcess P.DPA0) (hH0 : ComputableDeductiveProcess P.DPH0)
    (hq : Computable fun p : ℕ × ℕ => P.quotedA p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (P.e p.1).e p.2)
    (hX : LUV.MachineThresholdCodeSeq P.XH)
    (hσ : Computable fun p : ℕ × ℕ => (P.σ p.1).e p.2) :
    IsLogicalInductor (jointA P) (jointDPA P) := by
  unfold jointA
  exact LIA_is_logical_inductor (jointDPA P) (jointDPA_computable P hU hA0 hH0 hq he hX hσ)

/-- **T5.1, `H`'s side: the market `H` of the two-way pair is a logical inductor over its process,
which reads `A`** — under `UniformLIAEvaluator`.
Source: mandate T5.1
Kind: C
Fidelity: variant: plain trader class
Hyps: (b) `UniformLIAEvaluator` -/
theorem jointH_inductor (P : TwoWaySpec) (hU : UniformLIAEvaluator)
    (hA0 : ComputableDeductiveProcess P.DPA0) (hH0 : ComputableDeductiveProcess P.DPH0)
    (hq : Computable fun p : ℕ × ℕ => P.quotedA p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (P.e p.1).e p.2)
    (hX : LUV.MachineThresholdCodeSeq P.XH)
    (hσ : Computable fun p : ℕ × ℕ => (P.σ p.1).e p.2) :
    IsLogicalInductor (jointH P) (jointDPH P) := by
  unfold jointH
  exact LIA_is_logical_inductor (jointDPH P) (jointDPH_computable P hU hA0 hH0 hq he hX hσ)

/-- **T5.1 (headline). The two-way pair exists under `UniformLIAEvaluator`:** for computable bases
free of the ledger family and satisfiable, a computable quoted family, computable schedules with
payout after the lookahead, and an e.c. `XH`, the staggered joint recursion yields a `TwoWayPair`
— each market FAF's LIA over its process of record, which reads the other market's output on
the given schedules. No Brouwer step beyond FAF's own; the one cost is the uniform evaluator.
The unconditional form is OPEN (`twoWayPair_exists`).
Source: [[route-sparse-schedule]] §9, §10 hypothesis 7 (vq-wiki-067); [[route-negative-introspective]] §4.4 (vq-wiki-2-017 (b)); [[deference-in-logical-induction-v6]] §5.2 (root-deference-037)
Kind: C
Fidelity: variant: plain trader class; FAF quotes exact
Hyps: (b) `UniformLIAEvaluator` (FAF private `liaPrefixFromStagesAtFuel_prim`; API request) -/
noncomputable def twoWayPair_of_uniform (P : TwoWaySpec) (hU : UniformLIAEvaluator)
    (hA0 : ComputableDeductiveProcess P.DPA0) (hH0 : ComputableDeductiveProcess P.DPH0)
    (hq : Computable fun p : ℕ × ℕ => P.quotedA p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (P.e p.1).e p.2)
    (hX : LUV.MachineThresholdCodeSeq P.XH)
    (hσ : Computable fun p : ℕ × ℕ => (P.σ p.1).e p.2)
    (hfreeA : TagFreeProcess (cleanroomBaseTag + ledgerFamily) P.DPA0)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (P.DPA0.D n))
    (hfreeH : TagFreeProcess (cleanroomBaseTag + ledgerFamily) P.DPH0)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (P.DPH0.D n)) : TwoWayPair :=
  twoWayPair_of_inductors P (jointA_inductor P hU hA0 hH0 hq he hX hσ)
    (jointH_inductor P hU hA0 hH0 hq he hX hσ)
    (processFreeOf_ledgerSchedule_of_tagFree hfreeA) hworldA
    (processFreeOf_ledgerSchedule_of_tagFree hfreeH) hworldH

/-! ## 8. T5.3: the witness spec over the paper process -/

/-- **T5.3's spec:** both bases `paperDP 𝗜𝚺₁`, `H` reads `A`'s prices of the day-varying atoms
`⟨0, ⟨j, n⟩⟩` published the next day, `A` reads `H`'s day-`(n+1)` expectations of `cleanX n`
published at `n + 2` (`payoutSchedule`; payout after the lookahead by `payout_after_deferral`).
Source: mandate T5.3
Kind: D
Fidelity: n/a -/
noncomputable def paperTwoWaySpec : TwoWaySpec where
  DPA0 := paperDP 𝗜𝚺₁
  DPH0 := paperDP 𝗜𝚺₁
  quotedA := witnessQuoted
  e := fun _ => PublicationSchedule.succ
  XH := cleanX
  f := succDeferral
  σ := fun _ => payoutSchedule
  payout_after_lookahead := fun _ n => payout_after_deferral n

/-- **T5.3 (N+ for the conditional theorem): the two-way pair over `paperDP 𝗜𝚺₁`, under
`UniformLIAEvaluator`.** Every other hypothesis of `twoWayPair_of_uniform` is discharged from
FAF's facts (`paperDP_computable`, `paperDP_cleanroomFree`, `paperDP_hworld`) and
`li-quote-lane`'s witnesses (`witnessQuoted_computable`, `cleanX_codes`, the schedules). A discharge
of the hypothesis makes `twoWayPair_exists` `proved` with no further work.
Source: mandate T5.3
Kind: N+
Fidelity: variant: plain trader class
Hyps: (b) `UniformLIAEvaluator` -/
noncomputable def paperTwoWayPair_of_uniform (hU : UniformLIAEvaluator) : TwoWayPair :=
  twoWayPair_of_uniform paperTwoWaySpec hU (paperDP_computable 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁)
    witnessQuoted_computable succSchedule_computable cleanX_codes payoutSchedule_computable
    ((paperDP_cleanroomFree 𝗜𝚺₁).tagFree (Nat.le_add_right _ _)) (paperDP_hworld 𝗜𝚺₁)
    ((paperDP_cleanroomFree 𝗜𝚺₁).tagFree (Nat.le_add_right _ _)) (paperDP_hworld 𝗜𝚺₁)

/-- **N+ grounds (unconditional): the two jointly defined processes differ.** At any stage `s ≥ 1`
large enough to carry the code of `-1`, `H`'s process holds the affirmed ledger literal of day
`s − 1` (published the next day, `s`), while `A`'s process does not (its day-`(s−1)` entries are
published at `s + 1`, and `paperDP 𝗜𝚺₁` is cleanroom-free).
Source: mandate T5.3 ("prove the two jointly defined processes differ")
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperTwoWay_processes_differ (s : ℕ) (hs1 : 1 ≤ s)
    (hs : Encodable.encode (-1 : ℚ) ≤ s) :
    (jointDPH paperTwoWaySpec).D s ≠ (jointDPA paperTwoWaySpec).D s := by
  intro heq
  set P := paperTwoWaySpec with hP
  have hmemH : (ledgerFamily, ledgerPayload 0 (s - 1) (Encodable.encode (-1 : ℚ)), true) ∈
      (ledgerSchedule (aA P) P.e).lits s := by
    rw [ledgerSchedule_mem_iff]
    refine ⟨by omega, by omega, hs, ?_, ?_⟩
    · show s - 1 + 1 ≤ s
      omega
    · have : (-1 : ℚ) < aA P 0 (s - 1) := by linarith [(aA_mem P 0 (s - 1)).1]
      simp [this]
  have hin : freshAtom ledgerFamily (ledgerPayload 0 (s - 1) (Encodable.encode (-1 : ℚ))) ∈
      (jointDPH P).D s := by
    unfold jointDPH
    rw [ledgerProcess_D, Finset.mem_union]
    exact Or.inr (Finset.mem_image.mpr ⟨_, by rw [← ledgerSchedule_lits]; exact hmemH, rfl⟩)
  rw [heq] at hin
  unfold jointDPA at hin
  rw [ledgerProcess_D, Finset.mem_union] at hin
  rcases hin with h | h
  · exact (paperDP_cleanroomFree 𝗜𝚺₁ s _ h).freshAtomCode_notMem ledgerFamily
      (ledgerPayload 0 (s - 1) (Encodable.encode (-1 : ℚ))) (by simp [freshAtom])
  · obtain ⟨⟨f', p', b'⟩, hx, hx'⟩ := Finset.mem_image.mp h
    rw [← ledgerSchedule_lits] at hx
    cases b' with
    | false => exact absurd hx' (by simp [freshAtom])
    | true =>
      simp only [literalOf_true] at hx'
      obtain ⟨rfl, rfl⟩ := freshAtom_inj.mp hx'
      exact ledgerLuv_absent_before_payout (aH P) P.σ 0 (s - 1) (-1 : ℚ) true
        (by show s < s - 1 + 2; omega) hx

/-- Some stage separates the two processes (the code of `-1` is some natural number).
Source: mandate T5.3
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperTwoWay_processes_differ' :
    ∃ s, (jointDPH paperTwoWaySpec).D s ≠ (jointDPA paperTwoWaySpec).D s :=
  ⟨max 1 (Encodable.encode (-1 : ℚ)), paperTwoWay_processes_differ _ (le_max_left _ _)
    (le_max_right _ _)⟩

/-- **N+ grounds (unconditional): both polarities occur in both ledgers**, for every item and day
(`r = -1` affirmed, `r = 2` denied).
Source: mandate T5.3 ("both ledgers carry both polarities")
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperTwoWay_both_polarities (j n : ℕ) :
    ((∃ s, (ledgerFamily, ledgerPayload j n (Encodable.encode (-1 : ℚ)), true) ∈
        (ledgerSchedule (aA paperTwoWaySpec) paperTwoWaySpec.e).lits s) ∧
      ∃ s, (ledgerFamily, ledgerPayload j n (Encodable.encode (2 : ℚ)), false) ∈
        (ledgerSchedule (aA paperTwoWaySpec) paperTwoWaySpec.e).lits s) ∧
    ((∃ s, (ledgerFamily, ledgerPayload j n (Encodable.encode (-1 : ℚ)), true) ∈
        (ledgerSchedule (aH paperTwoWaySpec) paperTwoWaySpec.σ).lits s) ∧
      ∃ s, (ledgerFamily, ledgerPayload j n (Encodable.encode (2 : ℚ)), false) ∈
        (ledgerSchedule (aH paperTwoWaySpec) paperTwoWaySpec.σ).lits s) :=
  ⟨ledgerSchedule_both_polarities _ _ (aA_mem paperTwoWaySpec) j n,
    ledgerSchedule_both_polarities _ _ (aH_mem paperTwoWaySpec) j n⟩

end Cleanroom.Li.LiCoupledPair.A
