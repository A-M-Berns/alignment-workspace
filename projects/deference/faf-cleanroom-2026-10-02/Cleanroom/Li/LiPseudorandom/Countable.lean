import LogicalInduction.Construction.MachineTraderEnumeration
import LogicalInduction.Construction.Statistics.SettlementCompiler
import LogicalInduction.Properties.Pseudorandomness
import Mathlib.Computability.PartrecCode

/-!
# `li-pseudorandom` — T2: FAF's P-generable weightings form a countable class

Two forms, both proved:

* `Countable {W : ℕ → EF // PGenerableWeighting W}` (`pgenerable_countable`), by the injection
  `codeOf : W ↦ Nat.Partrec.Code` of the chosen token stream of `W.polySeg`: FAF's
  `MachineTokenStream.primrec` makes the stream primitive recursive, hence the graph of some
  code; `UnRpnContractsTo` at `rest := []` determines the serialization from the stream and
  `EF.serialize_injective` the feature.
* **The enumeration of record** `genWeighting : ℕ → (ℕ → EF)`, an *explicit, primitive
  recursive* function (`genWeighting_primrec`) covering every P-generable weighting exactly
  (`genWeighting_covers`): index `j` names a machine description and a polynomial clock
  (FAF's `MachineTraderProgram.index`), `machineTokens j n` runs that machine on the unary day
  `n` under that clock and reads off its digit output (`[]` on timeout), `undigitize` turns the
  digits into the token list, `unRpn` contracts the sentence blocks, and FAF's serialization
  decoder `efFromSerializedTokens` parses the result as an `EF` (`EF.const 0` if malformed).
  Coverage is FAF's own coverage bridge (`exists_desc_computesInTime_clock`,
  `machineTokens_eq_of_computesInTime`, `lt_clock_succ`): the `Complexity.FP` witness of
  `W.polySeg` is computed exactly, on every day, by some clocked index.

**Repair round 1.** The first version of `genWeighting` was
`fun k => (Classical.choose (exists_surjective_nat {W // PGenerableWeighting W}) k).1`, a
surjection chosen by `Classical.choice`. Both round-1 audits showed (probes
`audit-r1-probes/EnumDependence.lean`, `OrderDependence.lean`) that the diagonal depends on the
*order* of the enumeration, so the family of record was whatever sequence the chosen surjection
produced, and `Computable (truthStar …)` (T7) was not a provable statement about it. The
enumeration is now the explicit machine enumeration above; nothing about it is chosen, and it is
primitive recursive. T5 uses only `genWeighting_covers`, so no statement of T1–T6, T8 or T9 changed.

What was dropped: `genWeighting_pgenerable` (every enumerated progression is P-generable). It is
false for the explicit enumeration — a garbage index yields *some* `EF` progression, not
necessarily one satisfying `PGenerableWeighting`'s rank and closure clauses — and nothing used it:
the diagonal defeats every rule in the enumeration whether or not it is P-generable, and the
theorems quantify over the P-generable ones, which are all covered.

This is the package's one file importing `LogicalInduction.Construction.MachineTraderEnumeration`
(plan §0.5). It also imports `Construction.Statistics.SettlementCompiler` for FAF's
`efFromSerializedTokens` (the decoder FAF's own compilers use to invert `EF.serialize`); that
module is already in `Family.lean`'s import closure through `HistoricalMaturity`.
-/

namespace Cleanroom.Li.LiPseudorandom

open LogicalInduction LogicalInduction.MachineExec

/-! ## First form: countability through a code for the token stream -/

/-- The (chosen) machine token stream that a P-generable weighting's serializations contract from.
Source: none: infrastructure (T2)
Kind: D
Fidelity: n/a -/
noncomputable def PGenerableWeighting.stream {W : ℕ → EF} (h : PGenerableWeighting W) :
    ℕ → List ℕ :=
  Classical.choose h.polySeg

/-- The chosen stream is machine-metered and contracts to the serializations.
Source: none: infrastructure (T2)
Kind: L
Fidelity: n/a -/
lemma PGenerableWeighting.stream_spec {W : ℕ → EF} (h : PGenerableWeighting W) :
    MachineTokenStream (PGenerableWeighting.stream h) ∧
      ∀ z, UnRpnContractsTo (PGenerableWeighting.stream h z) ((W z).serialize) :=
  Classical.choose_spec h.polySeg

/-- A machine-metered token stream is the graph of a partial recursive code: some
`c : Nat.Partrec.Code` has `c.eval n = some (encode (t n))` for all `n`. Through FAF's
`MachineTokenStream.primrec` and Mathlib's `Nat.Partrec.Code.exists_code`.
Source: FAF `MachineTokenStream.primrec`; Mathlib `Nat.Partrec.Code.exists_code`
Kind: L
Fidelity: n/a -/
lemma exists_code_of_machineTokenStream {t : ℕ → List ℕ} (h : MachineTokenStream t) :
    ∃ c : Nat.Partrec.Code, ∀ n, c.eval n = Part.some (Encodable.encode (t n)) := by
  have hc : Computable t := (MachineTokenStream.primrec h).to_comp
  have hpart : Nat.Partrec fun n => Part.bind (Encodable.decode (α := ℕ) n)
      fun a => ((t : ℕ →. List ℕ) a).map Encodable.encode := hc.partrec
  obtain ⟨c, hc'⟩ := Nat.Partrec.Code.exists_code.1 hpart
  refine ⟨c, fun n => ?_⟩
  rw [hc']
  simp [PFun.coe_val]

/-- A code for the token stream of a P-generable weighting (chosen).
Source: none: infrastructure (T2)
Kind: D
Fidelity: n/a -/
noncomputable def codeOf (W : {W : ℕ → EF // PGenerableWeighting W}) : Nat.Partrec.Code :=
  Classical.choose (exists_code_of_machineTokenStream (PGenerableWeighting.stream_spec W.2).1)

/-- The chosen code computes the encoded token stream.
Source: none: infrastructure (T2)
Kind: L
Fidelity: n/a -/
lemma codeOf_spec (W : {W : ℕ → EF // PGenerableWeighting W}) (n : ℕ) :
    (codeOf W).eval n = Part.some (Encodable.encode (PGenerableWeighting.stream W.2 n)) :=
  Classical.choose_spec (exists_code_of_machineTokenStream (PGenerableWeighting.stream_spec W.2).1) n

/-- A token list contracts to at most one output (`rest := []` and cancel).
Source: FAF `UnRpnContractsTo` (`Framework/Emission/RpnSentence.lean`)
Kind: L
Fidelity: n/a -/
lemma UnRpnContractsTo.unique {ts a b : List ℕ} (ha : UnRpnContractsTo ts a)
    (hb : UnRpnContractsTo ts b) : a = b := by
  have h1 := ha []
  have h2 := hb []
  rw [h1] at h2
  exact List.append_cancel_right h2

/-- **The code determines the weighting**: `codeOf` is injective on the P-generable subtype.
Source: mandate T2 (route)
Kind: P
Fidelity: n/a -/
theorem codeOf_injective : Function.Injective codeOf := by
  intro W W' h
  have hs : PGenerableWeighting.stream W.2 = PGenerableWeighting.stream W'.2 := by
    funext n
    have h1 := codeOf_spec W n
    rw [h, codeOf_spec W'] at h1
    exact Encodable.encode_injective (Part.some_inj.1 h1).symm
  apply Subtype.ext
  funext n
  apply EF.serialize_injective
  have h1 := (PGenerableWeighting.stream_spec W.2).2 n
  have h2 := (PGenerableWeighting.stream_spec W'.2).2 n
  rw [hs] at h1
  exact UnRpnContractsTo.unique h1 h2

/-- **T2.** FAF's P-generable weightings form a countable class.
Source: mandate T2; FAF `PGenerableWeighting` (`def:ece`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem pgenerable_countable : Countable {W : ℕ → EF // PGenerableWeighting W} :=
  codeOf_injective.countable

/-- `pgenerable_countable` as an instance.
Source: mandate T2
Kind: L
Fidelity: n/a -/
instance instCountablePGenerable : Countable {W : ℕ → EF // PGenerableWeighting W} :=
  pgenerable_countable

/-- The class is inhabited: the constant feature `EF.const 0` is P-generable
(FAF `constantRatFeature_generated`). The degenerate member; plumbing, not a non-vacuity witness.
Source: FAF `AffineCombination.constantRatFeature_generated`
Kind: L
Fidelity: n/a -/
instance instNonemptyPGenerable : Nonempty {W : ℕ → EF // PGenerableWeighting W} :=
  ⟨⟨AffineCombination.constantRatFeature 0,
    (AffineCombination.constantRatFeature_generated (fun _ _ => 0) 0).toWeighting⟩⟩

/-! ## Second form: the explicit, primitive recursive enumeration of record -/

/-- **The enumeration of record of P-generable weightings** (T2, second form). Index `j` names a
machine description and a polynomial clock (FAF's `MachineTraderProgram.index`); day `n`'s
feature is the described machine's clocked output on the unary day `n` (`machineTokens j n`,
`[]` on timeout), un-digitized, un-RPN'd, and parsed by FAF's serialization decoder
(`efFromSerializedTokens`, `EF.const 0` if malformed). Explicit and primitive recursive
(`genWeighting_primrec`); covers every P-generable weighting exactly (`genWeighting_covers`).
A garbage index yields some `EF` progression that need not be P-generable — which no theorem
needs (T5 quantifies over the P-generable weightings and uses only coverage).
Source: mandate T2; FAF `machineTokens`, `undigitize`, `unRpn`, `efFromSerializedTokens`
Kind: D
Fidelity: exact (repair round 1: replaces a `Classical.choose`d surjection) -/
def genWeighting (j : ℕ) : ℕ → EF :=
  fun n => efFromSerializedTokens (unRpn (undigitize (machineTokens j n)))

/-- **The enumeration of record is primitive recursive** in `(j, n)`: FAF's
`primrec_machineTokens`, `undigitize_prim`, `unRpn_prim` and `efFromSerializedTokens_prim`
composed. This is the "computable presentation" the first version lacked: the rules the
diagonal defeats are now given by a program, so `Computable (truthStar …)` (T7) is a statement
whose only remaining obstacle is the LIA evaluator (see `Computable.lean`).
Source: mandate T2/T7; FAF `primrec_machineTokens`, `undigitize_prim`, `unRpn_prim`,
`efFromSerializedTokens_prim`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem genWeighting_primrec : Primrec₂ genWeighting := by
  unfold Primrec₂ genWeighting
  exact efFromSerializedTokens_prim.comp (unRpn_prim.comp (undigitize_prim.comp
    primrec_machineTokens))

/-- The enumeration of record is computable in `(j, n)` (corollary of `genWeighting_primrec`).
Source: mandate T7
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem genWeighting_computable : Computable₂ genWeighting :=
  genWeighting_primrec.to_comp

/-- **Every P-generable weighting is enumerated, exactly.** The `Complexity.FP` witness of
`W.polySeg` names a description and a clock (FAF `exists_desc_computesInTime_clock`); at the
index carrying that description and a dominating clock, `machineTokens` reproduces the witness's
digit output on every day (FAF `machineTokens_eq_of_computesInTime`), whose `decodeBits` is the
token stream `s`; `unRpn (s n)` is `(W n).serialize` (`UnRpnContractsTo.unRpn_eq`); and the
decoder inverts `serialize` (`efFromSerializedTokens_serialize`).
Source: mandate T2; FAF's coverage bridge (`Construction/Descriptions.lean`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem genWeighting_covers : ∀ W, PGenerableWeighting W → ∃ j, genWeighting j = W := by
  intro W hW
  obtain ⟨s, ⟨F, hF, -, hdec⟩, hcontract⟩ := hW.polySeg
  obtain ⟨d, a, k, T, hd, hak⟩ := exists_desc_computesInTime_clock hF
  refine ⟨MachineTraderProgram.index ⟨d, a + 1, k⟩, funext fun n => ?_⟩
  have htok : machineTokens (MachineTraderProgram.index ⟨d, a + 1, k⟩) n
      = bitsToDigits (F (unaryDay n)) := by
    refine machineTokens_eq_of_computesInTime (T := T) ?_ n ?_
    · rw [progDesc_index]; exact hd
    · rw [progClock_index, length_unaryDay]; exact lt_clock_succ (hak n)
  show efFromSerializedTokens (unRpn (undigitize (machineTokens _ n))) = W n
  rw [htok]
  have hs : undigitize (bitsToDigits (F (unaryDay n))) = s n := hdec n
  rw [hs, (hcontract n).unRpn_eq, efFromSerializedTokens_serialize]

/-- The enumeration of record is a surjection onto the P-generable subtype (a second proof of
`pgenerable_countable`, from the explicit enumeration).
Source: mandate T2
Kind: L
Fidelity: n/a -/
theorem genWeighting_surjective_subtype :
    ∀ W : {W : ℕ → EF // PGenerableWeighting W}, ∃ j, genWeighting j = W.1 :=
  fun W => genWeighting_covers W.1 W.2

end Cleanroom.Li.LiPseudorandom
