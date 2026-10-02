import Cleanroom.Found.LiQuoteLane.Defs
import LogicalInduction.Framework.Emission.Computable

/-!
# `li-quote-lane` · Codes: the ledger LUV family is efficiently codeable (T1.3)

The e.c. certificate every downstream `provind` / `cee` / `wubexp` use consumes: one poly-fueled
program emits the encoded threshold sentence `⌜α_{j,n} > i/k⌝` from the packed query
`⟨n, ⟨k, i⟩⟩`. The sentence is one atom whose code is
`⟨1, ⟨9 + 3, ⟨n, ⟨j, ⌜i/k⌝⟩⟩⟩⟩ + 1` (Foundation's `Formula.atom` shell around the fresh-atom
code), so the emitter is FAF's `gcd`-reduced quotient emitter `encode_natDiv_polyFueled` inside a
fixed pair shell — exactly the proof of FAF's `quoteAtom_mesh_encode_polyFueled`
(`Construction/Quotation/MarketQuoteCodes.lean`) with the tag-2 quotation shell replaced by the
fresh family. From the whole-value (`PolyFueled`) form the machine reading follows by FAF's
`RpnThresholdCodeSeq.ofPolyThresholdCodeSeq` and `RpnSentenceCodes.toMachine`.

Scope: one-way (a property of the reader's language alone).
-/

namespace Cleanroom.Found.LiQuoteLane

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-- The encoded ledger threshold sentence in closed shell form.
Source: none: infrastructure (FAF `encode_quoteAtom`)
Kind: L
Fidelity: n/a -/
lemma encode_ledgerLuv_gt (j n : ℕ) (r : ℚ) :
    Encodable.encode ((ledgerLuv j n).gt r) =
      Nat.pair 1 (Nat.pair (cleanroomBaseTag + ledgerFamily)
        (Nat.pair n (Nat.pair j (Encodable.encode r)))) + 1 := rfl

/-- **T1.3, whole-value form.** One poly-fueled program emits `⌜α_{j,n} > i/k⌝`'s code from
`⟨n, ⟨k, i⟩⟩`: FAF's `PolyThresholdCodeSeq`.
Source: mandate T1.3; FAF `quoteAtom_mesh_encode_polyFueled` (the same shell argument)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem ledgerLuv_polyThresholdCodeSeq (j : ℕ) :
    LUV.PolyThresholdCodeSeq (fun n => ledgerLuv j n) := by
  -- Query `m = ⟨n, ⟨k, i⟩⟩`: day `n`, denominator `k`, numerator `i`.
  have hn := PolyFueled.left
  have hk := PolyFueled.left.comp PolyFueled.right
  have hi := PolyFueled.right.comp PolyFueled.right
  obtain ⟨cmesh, meshPF⟩ := encode_natDiv_polyFueled hi hk
  have fullPF := ((PolyFueled.const 1).pair
    ((PolyFueled.const (cleanroomBaseTag + ledgerFamily)).pair
      (hn.pair ((PolyFueled.const j).pair meshPF)))).succ_comp
  exact ⟨_, fullPF.of_eq (fun m => (encode_ledgerLuv_gt j m.unpair.1 _).symm)⟩

/-- **T1.3 (headline). The ledger LUV family is e.c.**: `LUV.MachineThresholdCodeSeq (fun n =>
ledgerLuv j n)`, the certificate `ExpectedFutureExpectationQuote.quote_codes`,
`lic_expect_combination_provind_*`, `BoundedSequence.wubexp` and `expectAffineSeq_polySequence`
consume. Proved, not `decide`d: the whole-value emitter is composed from FAF's `PolyFueled`
calculus and the machine reading is FAF's bridge. Scope: one-way.
Source: mandate T1.3; [[setting-and-notation]] lines 50–71 ("poly-size template plus numeral")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem ledgerLuv_thresholdCodes (j : ℕ) :
    LUV.MachineThresholdCodeSeq (fun n => ledgerLuv j n) :=
  RpnSentenceCodes.toMachine
    (LUV.RpnThresholdCodeSeq.ofPolyThresholdCodeSeq (ledgerLuv_polyThresholdCodeSeq j))

/-- The single ledger LUV `α_{j,n}` is machine-codeable (the fixed-`n` reading, for endpoints
stated at one LUV).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ledgerLuv_thresholdCodes_single (j n : ℕ) : (ledgerLuv j n).MachineThresholdCodes := by
  have hquery : PolyFueled _ (fun m : ℕ => Nat.pair n m) :=
    (PolyFueled.const n).pair PolyFueled.id
  exact ((ledgerLuv_thresholdCodes j).comp (UnaryRuler.of_polyFueled hquery)).of_eq
    (fun m => by simp)

end Cleanroom.Found.LiQuoteLane
