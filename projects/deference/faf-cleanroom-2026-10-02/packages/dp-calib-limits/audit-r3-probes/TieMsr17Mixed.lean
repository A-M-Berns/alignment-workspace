import Cleanroom.Decision.DpCalibLimits.WitnessesR2
import Cleanroom.Decision.DpCalibration.TieTree

/-!
# Audit r3 (adversarial) probe — `t1_msr17_instance`'s conclusion is Levi-vacuous; the mixed
tie on `tieTree` is where MSR ⊆ MSR¹⁷ has content

`t1_msr17_instance` (`WitnessesR2.lean`, N+) inhabits the four hypotheses of
`msr17At_of_msrAt_recorded` on `t1` with the deterministic `δ_b`. Part 1 shows its conclusion
`MSR¹⁷` follows from recording + determinism alone (`tEdtAt_of_deterministic_recorded`, the
package's own `levi_vacuity`), without `MSRAt`: at a deterministic label `A_d^+ = {C(d)}` and
`T_EDT` is vacuous, so the instance does not exercise the inclusion's content (the MSR argmax over
realizable acts containing the `A_d^+` argmax). Part 2 supplies the instance that does: on
`dp-calibration`'s `tieTree` with `procQ ½` (not deterministic), both acts are supported and
realized, their tremble-pinned values tie at `5 = 5` with *different* act-conditional laws (a sure
`5` against a fair `0/10` coin), `MSRAt` is a genuine two-act comparison, `A_d^+ = {a, b}` so
`T_EDT` checks both supported acts, and `MSR¹⁷` follows through the theorem.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-! ## Part 1: `t1_msr17_instance`'s conclusion without `MSRAt` -/

theorem t1_msr17_conclusion_from_levi :
    MSR17At t1ActEv procB1 (fun _ => t1BStrictState) () := by
  have hpos : 0 < nu procB1 t1 (t1Obs ()) := by
    show 0 < nu procB1 t1 Finset.univ; exact nu_univ_pos _ _
  have hs : StrictOCAt (fun _ => t1BStrictState) t1Obs procB1 t1 () :=
    strictOCAt_calibratedState t1Obs procB1 t1 (fun _ => t1BStrictState) () hpos rfl
  exact (tEdtAt_of_deterministic_recorded t1Obs procB1 t1 (s := fun _ => t1BStrictState)
    (actEv := t1ActEv) .b rfl (t1_recordsFor procB1) hpos hs).2

/-! ## Part 2: the mixed tie -/

/-- `procQ ½` is not deterministic. -/
theorem tieProc_not_deterministic : ¬ Proc.IsDeterministic tieProc := by
  intro h
  obtain ⟨a, ha⟩ := h ()
  have := congrArg (fun m : FinDistr ℚ Act2 => m.w .a) ha
  cases a <;> simp [tieProc, procQ, FinDistr.act2] at this

/-- Both act events are realized under `procQ ½` on `tieTree`. -/
theorem tieProc_realized (y : Act2) : 0 < nu tieProc tieTree (tieActEv () y ∩ tieObs ()) := by
  simp only [tieObs, Finset.inter_univ]
  rw [tieTree_nu]
  cases y <;> simp [tieActEv, tieProc, procQ, FinDistr.act2] <;> norm_num

/-- The tremble-pinned values of both acts are `5`. -/
theorem tieProc_limitVals (y : Act2) : limitVal tieProc tieTree (tieActEv () y ∩ tieObs ()) = 5 := by
  rw [limitVal_eq_of_pos _ _ _ (tieProc_realized y)]
  have h := tieState_V tieProc (by norm_num [tieProc, procQ, FinDistr.act2])
    (by norm_num [tieProc, procQ, FinDistr.act2])
  simp only [tieState, calibratedState_V, Finset.inter_univ] at h
  simp only [tieObs, Finset.inter_univ]
  unfold condExp
  cases y
  · exact h.1
  · exact h.2

/-- `procQ ½` is MSR on `tieTree`: both supported acts are realized and tie at `5`. -/
theorem tieProc_msrAt : MSRAt tieObs tieActEv tieProc tieTree () := by
  intro x _
  have hne : ∀ y, nuPoly tieProc tieTree (tieActEv () y ∩ tieObs ()) ≠ 0 := fun y hz => by
    have := coeff_zero_nuPoly tieProc tieTree (tieActEv () y ∩ tieObs ())
    rw [hz, Polynomial.coeff_zero] at this
    exact absurd this.symm (tieProc_realized y).ne'
  refine ⟨hne x, fun y _ => ?_⟩
  rw [tieProc_limitVals x, tieProc_limitVals y]

/-- **The mixed-tie instance of `msr17At_of_msrAt_recorded`**: on the recorded `tieTree` with the
non-deterministic `procQ ½`, the four hypotheses hold, `A_d^+ = {a, b}` (so `T_EDT` is not
vacuous), both acts are supported, and `MSR¹⁷` follows through the theorem. -/
theorem tie_msr17_mixed_instance :
    StrictOCAt (fun _ => tieState tieProc) tieObs tieProc tieTree () ∧
    RecordsFor tieObs tieActEv tieProc tieTree () ∧
    0 < nu tieProc tieTree (tieObs ()) ∧
    MSRAt tieObs tieActEv tieProc tieTree () ∧
    MSR17At tieActEv tieProc (fun _ => tieState tieProc) () ∧
    APlus (fun _ => tieState tieProc) tieActEv () = Finset.univ ∧
    (∀ a, 0 < (tieProc ()).w a) ∧ ¬ Proc.IsDeterministic tieProc := by
  have hpos : 0 < nu tieProc tieTree (tieObs ()) := by
    unfold tieObs; exact nu_univ_pos _ _
  have hs : StrictOCAt (fun _ => tieState tieProc) tieObs tieProc tieTree () :=
    strictOCAt_calibratedState tieObs tieProc tieTree _ () _ rfl
  have hrec := tieTree_recordsFor tieProc
  refine ⟨hs, hrec, hpos, tieProc_msrAt,
    msr17At_of_msrAt_recorded _ _ _ _ _ () hs hrec hpos tieProc_msrAt, tieProc_aPlus,
    fun a => by cases a <;> norm_num [tieProc, procQ, FinDistr.act2], tieProc_not_deterministic⟩

end Cleanroom.Decision.DpCalibLimits
