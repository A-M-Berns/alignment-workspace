import Cleanroom.Decision.DpReferentsCdt.Rows2
import Cleanroom.Decision.DpReferentsCdt.C2B
import Cleanroom.Found.DpCoreTree.ScreeningWitness

/-!
# `dp-referents-cdt` · audit r1 (adversarial) probe: C2-B′'s N+ witness assembled in Lean

Not imported by the library.

The ledger's C2-B′ rows (`c2B_of_recordsFor_uniform`, `c2B_of_recordsForDeviations`) cite
`mug_row` / `coinQuery` as the N+ witnesses "inhabiting `RecordsForDeviations`". For the mugging
the package proves `mug_actRecordingStructural` and `mug_actEvDisjoint`, but no lemma gives
Definition 7 recording for every label: `dp-core-tree`'s `mug1_recordsFor` is stated at the one
label `procQ (1/2)`, and the transfer to every procedure (`RecordsFor.of_fullSupport`) is left to
prose. This file composes it, applies C2-B′ at every label, and checks the conclusion against
`mug_row`'s independently computed `(−1, 0)`: the hypothesis package is inhabited by a
non-degenerate instance and the equality it yields is between genuine values, not junk `0`s.
-/

namespace Cleanroom.Decision.DpReferentsCdt.AuditR1Adversarial

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpReferentsCdt
open Finset

/-- `procQ (1/2)` has full support. -/
theorem procHalf_fullSupport : (procQ (1/2) (by norm_num) (by norm_num)).FullSupport := by
  intro _ a
  cases a <;> simp [procQ, FinDistr.act2] <;> norm_num

/-- **The mugging is Definition-7-recorded for every procedure**, from `dp-core-tree`'s
`mug1_recordsFor` at the full-support label `1/2` and `RecordsFor.of_fullSupport`. -/
theorem mug_recordsForAll : RecordsForAll mugObs mugActEv mugTree () := by
  intro C
  unfold mugTree
  exact RecordsFor.of_fullSupport procHalf_fullSupport (mug1_recordsFor 1 3) C

/-- C2-B′ (the `RecordsForDeviations` form) applies at every label of the mugging and its
conclusion agrees with `mug_row`'s `(−1, 0)`: a non-degenerate instance of the full package. -/
theorem mug_c2B_witness (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (∀ a, refR1State mugObs (procQ q h0 h1) mugTree () a =
      refR2Real mugActEv (procQ q h0 h1) mugTree () a) ∧
    refR1State mugObs (procQ q h0 h1) mugTree () .a = -1 ∧
    refR2Real mugActEv (procQ q h0 h1) mugTree () .b = 0 := by
  obtain ⟨-, -, hR1a, -, -, -, -, hR2b, -, -⟩ := mug_row q h0 h1
  refine ⟨fun a => c2B_of_recordsForDeviations mugObs mugActEv _ mugTree
    mug_actRecordingStructural mug_actEvDisjoint (fun _ => mug_recordsForAll _) a, hR1a, hR2b⟩

end Cleanroom.Decision.DpReferentsCdt.AuditR1Adversarial
