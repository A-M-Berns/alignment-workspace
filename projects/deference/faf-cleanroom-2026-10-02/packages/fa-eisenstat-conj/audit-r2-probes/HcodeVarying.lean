import Cleanroom.Fa.FaEisenstatConj.Defs
import Cleanroom.Found.LiQuoteLane.Codes

/-!
# Audit r2 (adversarial) probe · HcodeVarying

Evidence for the audit of `fa-eisenstat-conj` (`fa-eisenstat-conj-audit-r2-adversarial.md`).
Not imported by the library.

What it checks: the repair-round-1 rows `samPair_crossQuotePackage_seq`,
`samPair_beh_limitPoint_seq` (proved) and `samPair_beh_seq` (OPEN) take the uniform machine
certificate `hcode : LUV.MachineThresholdCodeSeq (fun n => samQuote f (φ n) n)` as a
hypothesis, and findings F17 / the ledger say it is "discharged at no varying instance in the
run". If `hcode` were uninhabitable for every non-constant `φ`, those rows would add nothing
over the fixed-sentence forms (vacuous beyond the constant case). This probe inhabits it at a
genuinely varying sentence sequence — the atom family `φ n := atom n`, FAF's own
"smallest sentence family that varies with the day" — at `succDeferral`, by the same poly-fueled
emitter as `li-quote-lane`'s `ledgerLuv_polyThresholdCodeSeq` with the day coordinate
succeeded and the sentence code `⌜atom n⌝ = ⟨1, n⟩ + 1` (FAF's `encode_atom`) written from the
day. So the `_seq` rows have content beyond the constant case, and F17's "next step" lemma is
within reach (this is its instance at the atom family).
-/

namespace Cleanroom.Fa.FaEisenstatConj

open LogicalInduction LO.Propositional Cleanroom.Found.LiQuoteLane Cleanroom.Bli.BliFound

/-- Probe: `hcode` at the varying sentence sequence `n ↦ atom n`, `f := succDeferral`. -/
theorem probe_samQuote_codes_succ_atom :
    LUV.MachineThresholdCodeSeq (fun n => samQuote succDeferral (Formula.atom n) n) := by
  refine RpnSentenceCodes.toMachine (LUV.RpnThresholdCodeSeq.ofPolyThresholdCodeSeq ?_)
  -- Query `m = ⟨n, ⟨k, i⟩⟩`: day `n`, denominator `k`, numerator `i`.
  have hn := PolyFueled.left
  have hk := PolyFueled.left.comp PolyFueled.right
  have hi := PolyFueled.right.comp PolyFueled.right
  obtain ⟨cmesh, meshPF⟩ := encode_natDiv_polyFueled hi hk
  -- `⌜atom n⌝ = ⟨1, n⟩ + 1`, written from the day.
  have hatom := ((PolyFueled.const 1).pair hn).succ_comp
  -- The pair shell of `⌜ledgerLuv ⌜atom n⌝ (n + 1) > i/k⌝`.
  have fullPF := ((PolyFueled.const 1).pair
    ((PolyFueled.const (cleanroomBaseTag + ledgerFamily)).pair
      (hn.succ_comp.pair (hatom.pair meshPF)))).succ_comp
  exact ⟨_, fullPF.of_eq (fun m => by
    rw [samQuote_apply, encode_ledgerLuv_gt, encode_atom]
    rfl)⟩

end Cleanroom.Fa.FaEisenstatConj
