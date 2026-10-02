import Cleanroom.Decision.DpFirstpersonSc.WitnessesNewcomb

/-!
Audit r3 (adversarial) probe for the T2(c) row (`WitnessesNewcomb.lean`): the row says the
cells are `License`, "which is the stamped audit verdict by T2(a) under the two guards
`0 < ν(O_d)`, `0 < μ(occ(d))` — both hold on every row (`tnV1_E_occ_mass`, `tnV2_occ_E`; not
discharged in the cells, audit r1 fidelity N3)". The two named lemmas cover `d_E`'s occurrence
mass only. This probe discharges the three the package does not state: `ν(O_F) = ¾` on V1
under `(1,2)`, and `ν(O_E) = ¼`, `ν(O_F) = ¾` on V2 under `(1,1)` (`p = ¾`); `μ(occ(d_F)) = 1`
on V1 and `μ(occ) = 1` at both V2 points follow from `tnV1_occ_F`/`tnV2_occ_E`/`tnV2_occ_F`
(`= univ`). With these, every T2(c) cell is the stamped audit verdict through
`audit_license_iff_nullDiff`, machine-checked. Not imported by the library.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFaithfulUdt
open Finset

/-- `ν(O_F) = ¾` on V1 at `p = ¾` under `(1,2)`. -/
theorem probe_tnV1_oneTwo_nu_F :
    nu tnOneTwo (tnV1 (3/4) (by norm_num) (by norm_num) 4 1) (tnObs .F) = 3 / 4 := by
  rw [nu_eq_sum, tnV1_sum]
  simp only [tnV1_world, tnV1_leafLaw, tnObs]
  simp [box_sum_univ, Fin.sum_univ_two, tnOneTwo] <;> norm_num

/-- `ν(O_E) = ¼` on V1 at `p = ¾` under `(1,2)` (for completeness; equals `tnV1_E_occ_mass`). -/
theorem probe_tnV1_oneTwo_nu_E :
    nu tnOneTwo (tnV1 (3/4) (by norm_num) (by norm_num) 4 1) (tnObs .E) = 1 / 4 := by
  rw [nu_eq_sum, tnV1_sum]
  simp only [tnV1_world, tnV1_leafLaw, tnObs]
  simp [box_sum_univ, Fin.sum_univ_two, tnOneTwo] <;> norm_num

/-- `ν(O_E) = ¼` on V2 at `p = ¾` under `(1,1)`. -/
theorem probe_tnV2_large_nu_E :
    nu procLarge (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) (tnObs .E) = 1 / 4 := by
  rw [nu_eq_sum, tnV2_sum]
  simp only [tnV2_world, tnV2_leafLaw, tnObs]
  simp [box_sum_univ, Fin.sum_univ_two, procLarge] <;> norm_num

/-- `ν(O_F) = ¾` on V2 at `p = ¾` under `(1,1)`. -/
theorem probe_tnV2_large_nu_F :
    nu procLarge (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) (tnObs .F) = 3 / 4 := by
  rw [nu_eq_sum, tnV2_sum]
  simp only [tnV2_world, tnV2_leafLaw, tnObs]
  simp [box_sum_univ, Fin.sum_univ_two, procLarge] <;> norm_num

/-- The occurrence masses at the three remaining cells are `1` (`occ = univ`). -/
theorem probe_occ_masses :
    mass tnOneTwo (tnV1 (3/4) (by norm_num) (by norm_num) 4 1) (occ .F _) = 1 ∧
    mass procLarge (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) (occ .E _) = 1 ∧
    mass procLarge (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) (occ .F _) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [tnV1_occ_F, mass_univ]
  · rw [tnV2_occ_E, mass_univ]
  · rw [tnV2_occ_F, mass_univ]

end Cleanroom.Decision.DpFirstpersonSc
