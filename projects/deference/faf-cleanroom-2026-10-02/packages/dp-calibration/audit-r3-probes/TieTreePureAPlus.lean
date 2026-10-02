import Cleanroom.Decision.DpCalibration.TieTree

/-!
# Audit round 3 (adversarial) probe: the pure labels in `tieTree_every_label_approved`

`tieTree_every_label_approved` says every `procQ q`, `q ∈ [0, 1]`, is strictly calibrated and
`T_EDT`-approved on the tie tree. For the pure labels the approval is the singleton case of
Definition 18 (`A_d^+ = {a}` for `δ_a`), i.e. Remark 3.9's vacuity, while for the interior
labels it is the tie `V(a) = 5 = V(b)` (`tieState_V`). This probe records the singleton fact so
the row's "every label" is read with the right mechanism per label. Not imported by the library.
-/

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Catalogue

/-- For `δ_a = procQ 1`, the strict state makes `b` subjectively impossible: `A^+ = {a}`. -/
theorem probe_tieTree_pureA_aPlus :
    APlus (fun _ => tieState tieProcA) tieActEv () = {Act2.a} := by
  ext x
  simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  obtain ⟨hpa, hpb⟩ := tieState_pr tieProcA
  cases x
  · rw [hpa]; norm_num [tieProcA, procQ]
  · rw [hpb]; norm_num [tieProcA, procQ]; decide

end Cleanroom.Decision.DpCalibration
