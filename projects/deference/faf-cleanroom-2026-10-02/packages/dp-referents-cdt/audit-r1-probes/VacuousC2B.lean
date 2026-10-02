import Cleanroom.Decision.DpReferentsCdt.C2B

/-!
# `dp-referents-cdt` · audit r1 (adversarial) probe: the positivity-free C2-B′ is satisfiable with
both sides junk

Not imported by the library.

`c2B_of_recordsFor_uniform` and `c2B_of_recordsForDeviations` carry no positivity hypothesis; the
docstring and ledger say that at a null denominator both sides are junk `0` and grade that reading
N−. This probe realises the degenerate model: a single leaf, `O_d = ∅`, empty action events.
F3′ structural, disjointness and Definition 7 recording for every procedure all hold vacuously
(no decision node, no `O_d`-leaf), and the conclusion reads `0 = 0` at every act. So the
theorem's non-vacuity rests entirely on its N+ witnesses (`mug_row`, `coinQuery`), as the ledger
says — the disclosure is accurate, and this file is the check that it is literal.
-/

namespace Cleanroom.Decision.DpReferentsCdt.AuditR1Adversarial

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpReferentsCdt
open Finset

/-- A single leaf. -/
def vTree : Tree Unit Unit (fun _ => Act2) ℚ := .leaf () 7

/-- `O_d = ∅`. -/
def vObs : Unit → Finset Unit := fun _ => ∅

/-- Empty action events. -/
def vActEv : (d : Unit) → Act2 → Finset Unit := fun _ _ => ∅

theorem v_structural : ActRecordingStructural vObs vActEv vTree () := by
  intro C _
  refine ⟨fun q => q.elim, ?_⟩
  intro ℓ _ hobs
  simp [vObs] at hobs

theorem v_disjoint : ActEvDisjoint vActEv () := by
  intro a b _
  simp [vActEv]

theorem v_recordsForAll : RecordsForAll vObs vActEv vTree () := by
  intro C ℓ _ hobs
  simp [vObs] at hobs

/-- Both sides of C2-B′ are junk `0` here: `ν_{C[d↦a]}(∅) = 0` and the real fiber is empty. -/
theorem v_both_junk (C : Proc Unit (fun _ => Act2) ℚ) (a : Act2) :
    refR1State vObs C vTree () a = 0 ∧ refR2Real vActEv C vTree () a = 0 := by
  constructor
  · unfold refR1State condExp paySum nu
    simp [vObs, worldEv]
  · unfold refR2Real realForced realReach
    have hfib : realFiber vActEv vTree () = ∅ := by
      ext q; exact q.elim
    simp [hfib]

/-- The theorem applies and says `0 = 0`. -/
theorem v_c2B_says_nothing (C : Proc Unit (fun _ => Act2) ℚ) (a : Act2) :
    refR1State vObs C vTree () a = refR2Real vActEv C vTree () a :=
  c2B_of_recordsForDeviations vObs vActEv C vTree v_structural v_disjoint
    (fun m => v_recordsForAll _) a

end Cleanroom.Decision.DpReferentsCdt.AuditR1Adversarial
