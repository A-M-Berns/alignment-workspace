import Cleanroom.Deference.DefFrozenSibling.Defs
import LogicalInduction.Construction.Primcodable

/-!
# `def-frozen-sibling` · Computable: membership in `G` as a computable function of the day

The mandate's second half of D2 ("membership in `G` is decidable … and computable", kind C),
added in repair round 1 (audit r1 fidelity N11 / report §D2 "not shipped"). Light module
(imports `Defs` and FAF's `Construction/Primcodable`, nothing heavy).

`timely_computable`: for a system whose shared process is computable in FAF's sense
(`ComputableDeductiveProcess S.base`: one partial recursive program emits every stage) and whose
contract family, horizon, diagonal and tolerance schedule are computable functions of the day,
`n ↦ decide (Timely S ε n)` is computable — run the shared process to stage `F n`, test the
contract and its negation for membership (the sorted-list encoding of a `Finset Sentence`), read
off the decided value, and compare `|Y n − truthAt n|` with `ε n` in exact rational arithmetic
(FAF's `ratSub_prim`, `ratAbs_prim`, `ratLE_prim`). This is v6 §6's "run `D` to the finite stage
`F(n)` and check" as a theorem. It is **not** efficient computability: the sibling run to `F n`
that produces `Y n` is a hypothesis here (`hY`), and FAF's `UnaryRuler` (an FP indicator) is what
the on-`G` theorems need — finding F1 (membership is decidable, not FP in general) stands.

The two stage/membership lemmas re-prove `li-coupled-pair`'s `stage_computable` and
`finsetSentence_mem_prim` (its heavy `A/LedgerDecided.lean`, which imports the LIA compiler);
attribution in each docstring, as the package does for `def-tracking-pin`'s `Column` lemmas
(report §Deviations 1).
-/

namespace Cleanroom.Deference.DefFrozenSibling

open LogicalInduction LO.Propositional

/-! ## A. Stages and membership (re-proved from `li-coupled-pair`'s heavy module) -/

/-- The stages of a computable deductive process form a computable function (run the process
code; it is total on every day). Re-proof of `li-coupled-pair`'s `stage_computable`
(`A/LedgerDecided.lean`, heavy); the statement and proof are theirs.
Source: none: infrastructure (FAF `ComputableDeductiveProcess`; `li-coupled-pair` `stage_computable`)
Kind: L
Fidelity: n/a -/
theorem stage_computable' {DP : DeductiveProcess} (hDP : ComputableDeductiveProcess DP) :
    Computable DP.D := by
  obtain ⟨code, hcode⟩ := hDP
  have h1 : Partrec fun n : ℕ => code.eval n :=
    Nat.Partrec.Code.eval_part.comp (Computable.const code) Computable.id
  have h2 : Computable fun n => Encodable.encode (DP.D n) := h1.of_eq_tot hcode
  have h3 : Computable fun n =>
      (Encodable.decode (α := Finset Sentence) (Encodable.encode (DP.D n))).getD ∅ :=
    Computable.option_getD (Computable.decode.comp h2) (Computable.const ∅)
  exact h3.of_eq fun n => by simp [Encodable.encodek]

/-- Decoding the code of a `Finset Sentence` as a `List Sentence` gives a list with the same
members (FAF's `Finset Sentence` encoding is Mathlib's multiset encoding of the sorted list).
Re-proof of `li-coupled-pair`'s `finsetSentence_decode_list` (heavy module).
Source: none: infrastructure (FAF `sentenceFinsetEncode_eq`; Mathlib `Multiset.encodable`)
Kind: L
Fidelity: n/a -/
lemma finsetSentence_decode_list' (s : Finset Sentence) :
    ∃ l : List Sentence, Encodable.decode (α := List Sentence) (Encodable.encode s) = some l ∧
      ∀ φ, φ ∈ l ↔ φ ∈ s := by
  have h : Encodable.decode (α := Multiset Sentence) (Encodable.encode s) = some s.1 := by
    rw [sentenceFinsetEncode_eq]
    exact Encodable.encodek s.1
  change decodeMultiset (Encodable.encode s) = some s.1 at h
  unfold decodeMultiset at h
  cases hd : Encodable.decode (α := List Sentence) (Encodable.encode s) with
  | none => rw [hd] at h; simp at h
  | some l =>
    rw [hd] at h
    simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at h
    refine ⟨l, rfl, fun φ => ?_⟩
    rw [Finset.mem_def, ← h, Multiset.mem_coe]

/-- Membership in a `Finset Sentence` is primitive recursive (through the sorted-list encoding and
`List.idxOf`). Re-proof of `li-coupled-pair`'s `finsetSentence_mem_prim` (heavy module).
Source: none: infrastructure (`li-coupled-pair` `finsetSentence_mem_prim`)
Kind: L
Fidelity: n/a -/
lemma finsetSentence_mem_prim' :
    Primrec₂ fun (φ : Sentence) (s : Finset Sentence) => decide (φ ∈ s) := by
  have hl : Primrec fun s : Finset Sentence =>
      (Encodable.decode (α := List Sentence) (Encodable.encode s)).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp Primrec.encode) (Primrec.const [])
  have hidx : Primrec fun p : Sentence × List Sentence => decide (p.2.idxOf p.1 < p.2.length) :=
    Primrec.nat_lt.decide.comp (Primrec.list_idxOf.comp Primrec.fst Primrec.snd)
      (Primrec.list_length.comp Primrec.snd)
  refine (hidx.comp (Primrec.fst.pair (hl.comp Primrec.snd))).of_eq fun p => ?_
  obtain ⟨l, hl', hmem⟩ := finsetSentence_decode_list' p.2
  simp only [hl', Option.getD_some]
  rw [decide_eq_decide, List.idxOf_lt_length_iff]
  exact hmem p.1

/-! ## B. The fragments are computable functions of the day -/

/-- The stage at the horizon, `n ↦ base.D (F n)`, is computable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem horizonStage_computable (S : FrozenSystem) (hbase : ComputableDeductiveProcess S.base)
    (hF : Computable S.F.f) : Computable fun n => S.base.D (S.F.f n) :=
  (stage_computable' hbase).comp hF

/-- Membership of the contract in the horizon stage is computable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem contractMem_computable (S : FrozenSystem) (hbase : ComputableDeductiveProcess S.base)
    (hc : Computable S.contract) (hF : Computable S.F.f) :
    Computable fun n => decide (S.contract n ∈ S.base.D (S.F.f n)) :=
  finsetSentence_mem_prim'.to_comp.comp hc (horizonStage_computable S hbase hF)

/-- Membership of the contract's negation in the horizon stage is computable (FAF's
`sentenceNeg_prim`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem contractNegMem_computable (S : FrozenSystem) (hbase : ComputableDeductiveProcess S.base)
    (hc : Computable S.contract) (hF : Computable S.F.f) :
    Computable fun n => decide (∼S.contract n ∈ S.base.D (S.F.f n)) :=
  finsetSentence_mem_prim'.to_comp.comp (sentenceNeg_prim.to_comp.comp hc)
    (horizonStage_computable S hbase hF)

/-- **The decided clause is a computable function of the day**: `n ↦ decide (DecidedBy S n)` for a
computable shared process, contract family and horizon.
Source: [[frozen-deliberation-deference-v6]] §6 ("Membership is decidable (run `D` … to the finite stage `F(n)` and check)"); mandate D2 (the `Computable` form)
Kind: C
Fidelity: exact (unary-time computability, not FP — finding F1)
Hyps: (a) none (`hbase`, `hc`, `hF` are the data: which computable process, contracts, horizon) -/
theorem decidedBy_computable (S : FrozenSystem) (hbase : ComputableDeductiveProcess S.base)
    (hc : Computable S.contract) (hF : Computable S.F.f) :
    Computable fun n => decide (DecidedBy S n) := by
  refine (Computable.cond (contractMem_computable S hbase hc hF) (Computable.const true)
    (contractNegMem_computable S hbase hc hF)).of_eq fun n => ?_
  unfold DecidedBy
  by_cases h1 : S.contract n ∈ S.base.D (S.F.f n) <;>
    by_cases h2 : ∼S.contract n ∈ S.base.D (S.F.f n) <;> simp [h1, h2]

/-- **The decided value is a computable function of the day**: `n ↦ truthAt S n`.
Source: mandate D2 (the `Computable` form)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem truthAt_computable (S : FrozenSystem) (hbase : ComputableDeductiveProcess S.base)
    (hc : Computable S.contract) (hF : Computable S.F.f) : Computable (truthAt S) := by
  refine (Computable.cond (contractMem_computable S hbase hc hF) (Computable.const (1 : ℚ))
    (Computable.const (0 : ℚ))).of_eq fun n => ?_
  unfold truthAt
  by_cases h : S.contract n ∈ S.base.D (S.F.f n) <;> simp [h]

/-- The tolerance clause `|Y n − truthAt n| ≤ ε n` is a computable predicate of the day, for
computable `Y` and `ε` (FAF's exact rational primitives `ratSub_prim`, `ratAbs_prim`,
`ratLE_prim`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem toleranceClause_computable (S : FrozenSystem) (ε : ℕ → ℚ)
    (hbase : ComputableDeductiveProcess S.base) (hc : Computable S.contract)
    (hF : Computable S.F.f) (hY : Computable S.Y) (hε : Computable ε) :
    Computable fun n => decide (|S.Y n - truthAt S n| ≤ ε n) := by
  have hle : Primrec fun z : ℚ × ℚ => decide (z.1 ≤ z.2) := ratLE_prim.decide
  have hdiff : Computable fun n => |S.Y n - truthAt S n| :=
    ratAbs_prim.to_comp.comp (ratSub_prim.to_comp.comp hY (truthAt_computable S hbase hc hF))
  refine (hle.to_comp.comp (hdiff.pair hε)).of_eq fun n => ?_
  exact decide_eq_decide.mpr Iff.rfl

/-- **Membership in `G` is a computable function of the day** (mandate D2, second half; the
`Decidable` instance `timely_decidable` is the first): for a shared process computable in FAF's
sense, computable contracts, horizon, diagonal and tolerance schedule, `n ↦ decide (Timely S ε n)`
is computable — run the shared process to stage `F n`, test the contract and its negation, read
off the decided value, compare `|Y n − truthAt n|` with `ε n` exactly. **Not** efficient: the
diagonal `Y n` (a sibling run to the horizon) enters as the hypothesis `hY`, and the on-`G`
theorems need an FP indicator (`UnaryRuler`) of a sub-fragment — finding F1. At `onGSystem` and
`antiSystem` every hypothesis holds (`base0_computable`, `contract5` e.c., `succDeferral`,
`Y0_computable`/`Y1_computable`), but those instances live in the heavy modules and are not
restated here.
Source: [[frozen-deliberation-deference-v6]] §6 ("Membership is decidable (run `D` and `H^{[n]}` to the finite stage `F(n)` and check)"); mandate D2 (kind C, the `Computable` form); audit r1 fidelity N11
Kind: C
Fidelity: exact (unary-time computability; the sibling run is the hypothesis `hY`)
Hyps: (a) none (`hbase`, `hc`, `hF`, `hY`, `hε` are the data of the system; at the inhabitants of record they are theorems) -/
theorem timely_computable (S : FrozenSystem) (ε : ℕ → ℚ)
    (hbase : ComputableDeductiveProcess S.base) (hc : Computable S.contract)
    (hF : Computable S.F.f) (hY : Computable S.Y) (hε : Computable ε) :
    Computable fun n => decide (Timely S ε n) := by
  refine (Computable.cond (decidedBy_computable S hbase hc hF)
    (toleranceClause_computable S ε hbase hc hF hY hε) (Computable.const false)).of_eq fun n => ?_
  unfold Timely
  by_cases h1 : DecidedBy S n <;> by_cases h2 : |S.Y n - truthAt S n| ≤ ε n <;> simp [h1, h2]

end Cleanroom.Deference.DefFrozenSibling
