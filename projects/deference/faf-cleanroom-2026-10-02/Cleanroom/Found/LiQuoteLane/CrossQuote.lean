import Cleanroom.Found.LiQuoteLane.Ledger
import Cleanroom.Found.LiQuoteLane.Codes
import LogicalInduction.Properties.SelfTrust
import LogicalInduction.Properties.ExpectationAffine

/-!
# `li-quote-lane` · CrossQuote: consequences of the cross-market quote package (T2.2)

`CrossQuotePackage H DPA f X Y` (`Defs.lean`) is a hypothesis package; this file gives a dependent
the facts it wants without unpacking it: the self-instance from FAF's
`ExpectedFutureExpectationQuote` (`H = A`), and the `DeterminedViaTheory` /
`ApproxDeterminedViaTheory` / `WorldValued` / `BoundedSequence` inputs of
`lic_expect_combination_provind_{le,ge,eq}_ofDetermined` (`Construction/LUV/Endpoints.lean`),
`PolySequence.affine_provind_theory_*` (`Properties/AffineCoherence.lean`) and
`BoundedSequence.wubexp` (`Properties/ExpectationProperties.lean`), through `li-asymp-calc`'s
bridges. The ledger instance (T2.4, the mirror one-way pair) is `MirrorPair.lean`.

Scope: one-way.
-/

namespace Cleanroom.Found.LiQuoteLane

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Filter Topology

/-- **T2.2, the self-instance:** FAF's same-market `ExpectedFutureExpectationQuote P DP f X Y`
(`thm:cee`'s certificate) is a `CrossQuotePackage P DP f X Y` with `H = A = P` — the `N−` shape
(one market) every two-market theorem's witness must be graded against.
Source: FAF `ExpectedFutureExpectationQuote` (`Properties/SelfTrust.lean`); mandate T2.2
Kind: L
Fidelity: exact (same-market projection)
Hyps: (a) none -/
def ExpectedFutureExpectationQuote.toCross {P : History} {DP : DeductiveProcess}
    {f : DeferralFunction} {X Y : ℕ → LUV} (q : ExpectedFutureExpectationQuote P DP f X Y) :
    CrossQuotePackage P DP f X Y :=
  ⟨q.quote_codes, fun n v hv => q.reflected n v hv⟩

/-- **T2.2:** from `reflected`, FAF's `LUVCombination.DeterminedViaTheory` of the quote family at
`H`'s realized future expectations — the `hdet0` input of
`lic_expect_combination_provind_*_ofDetermined` and `BoundedSequence.wubexp`.
Source: mandate T2.2; `li-asymp-calc` `DeterminedVia.determinedViaTheory_ofLUV`
Kind: L
Fidelity: exact
Hyps: (c) the package's `reflected` (Σ₁-completeness of `Γ_A` about `H`; `li-coupled-pair`) -/
theorem CrossQuotePackage.determinedViaTheory {H : History} {DPA : DeductiveProcess}
    {f : DeferralFunction} {X Y : ℕ → LUV} (h : CrossQuotePackage H DPA f X Y) (A : History) :
    LUVCombination.DeterminedViaTheory (fun n => LUVCombination.ofLUV (Y n)) A DPA
      (fun n => (X n).expect H (f.f n)) :=
  DeterminedVia.determinedViaTheory_ofLUV A h.reflected

/-- **T2.2:** from `reflected`, FAF's `LUVCombination.WorldValued` of the quote family — the
`hwv` input of `lic_expect_combination_provind_*`.
Source: mandate T2.2; `li-asymp-calc` `DeterminedVia.worldValued_ofLUV`
Kind: L
Fidelity: exact
Hyps: (c) the package's `reflected` -/
theorem CrossQuotePackage.worldValued {H : History} {DPA : DeductiveProcess}
    {f : DeferralFunction} {X Y : ℕ → LUV} (h : CrossQuotePackage H DPA f X Y) :
    LUVCombination.WorldValued (fun n => LUVCombination.ofLUV (Y n)) DPA :=
  DeterminedVia.worldValued_ofLUV h.reflected

/-- **T2.2:** from `reflected`, the precision-`(n+1)` mesh of the quote family is
`ApproxDeterminedViaTheory` at the truths with error `1/(n+1)` — the input of `lic_wubaff` /
`affine_provind_theory_*`.
Source: mandate T2.2; `li-asymp-calc` `DeterminedVia.approxDetermined_mesh_ofLUV`
Kind: L
Fidelity: exact
Hyps: (c) the package's `reflected` -/
theorem CrossQuotePackage.approxDetermined_mesh {H : History} {DPA : DeductiveProcess}
    {f : DeferralFunction} {X Y : ℕ → LUV} (h : CrossQuotePackage H DPA f X Y) (A : History) :
    AffineCombination.ApproxDeterminedViaTheory
      (fun n => (LUVCombination.ofLUV (Y n)).meshAffine (n + 1)) A DPA
      (fun n => (X n).expect H (f.f n)) (fun n => 1 / ((n : ℝ) + 1)) :=
  DeterminedVia.approxDetermined_mesh_ofLUV A h.reflected

/-- The diagonal threshold mesh of a singleton combination `0 + 1·Y_n` is a `PolySequence` from
the family's e.c. certificate (FAF's `expectAffineSeq_polySequence` with the `1·` scale folded
in).
Source: none: infrastructure (FAF `LUV.expectAffineSeq_polySequence`)
Kind: L
Fidelity: n/a -/
noncomputable def ofLUV_mesh_polySequence (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y) :
    AffineCombination.PolySequence
      (fun n => (LUVCombination.ofLUV (Y n)).meshAffine (n + 1)) := by
  let cinv := Classical.choose encode_inv_nat_polyFueled
  have hinv := Classical.choose_spec encode_inv_nat_polyFueled
  have hindex := (UnaryRuler.unpairFst.pair (UnaryRuler.unpairFst.succ.pair UnaryRuler.unpairSnd))
  have hsentence := MachineSentenceCodes.comp hY hindex
  exact {
    termCount := fun n => n + 1
    coefficient := fun z => .mul (.const 1) (.const (1 / ((z.unpair.1 + 1 : ℕ) : ℚ)))
    sentence := fun z => (Y z.unpair.1).gt ((z.unpair.2 : ℚ) / ((z.unpair.1 + 1 : ℕ) : ℚ))
    termCount_poly := UnaryRuler.id.succ
    const_poly := MachineSpliceStream.serialize_const 0
    coefficient_poly := MachineSpliceStream.serialize_mul (MachineSpliceStream.serialize_const 1)
      (BigSpliceStream.serialize_const_comp ⟨_, hinv.comp PolyFueled.left.succ_comp⟩).toMachine
    sentence_poly := hsentence.of_eq (fun z => by simp)
    terms_eq := by
      intro n
      simp [LUVCombination.meshAffine, LUVCombination.ofLUV, AffineCombination.scale,
        LUV.expectAffine, List.map_map, Function.comp_def]
    const_rank := by intro n; simp [LUVCombination.meshAffine, LUVCombination.ofLUV]
    coefficient_rank := by intro n j hj; simp [EF.rank]
    const_closed := by intro n ρ V; simp [LUVCombination.meshAffine, LUVCombination.ofLUV]
    coefficient_closed := by intro z ρ V; simp [EF.denoteWith]
  }

/-- **T2.2:** from `quote_codes`, the quote family is a `LUVCombination.BoundedSequence` in any
market (`def:blcp`: polynomial mesh plus a uniform `L¹` bound, here `1`) — the `h` input of
`lic_expect_combination_provind_*` and `BoundedSequence.wubexp`.
Source: mandate T2.2; `li-asymp-calc` `l1Norm_ofLUV`
Kind: L
Fidelity: exact
Hyps: (a) none (uses only `quote_codes`) -/
noncomputable def CrossQuotePackage.boundedSequence {H : History} {DPA : DeductiveProcess}
    {f : DeferralFunction} {X Y : ℕ → LUV} (h : CrossQuotePackage H DPA f X Y) (A : History) :
    LUVCombination.BoundedSequence (fun n => LUVCombination.ofLUV (Y n)) A where
  poly := ⟨ofLUV_mesh_polySequence Y h.quote_codes⟩
  bounded := ⟨1, fun n => (l1Norm_ofLUV (Y n) A).2.le⟩

end Cleanroom.Found.LiQuoteLane
