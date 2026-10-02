import Cleanroom.Decision.DpCalibration.LimitTie

/-!
# Audit round 3 (adversarial) probe: where on `limitTie` is D1's approval a real tie?

`limitTie_limitStateEdt` says D1 approves every label `(m; δ_{a'})`. This probe separates the
two mechanisms behind that statement:

* for the pure label `δ_b`, the limit state at `d` has `A_d^+ = {b}` — `a` is subjectively
  impossible, so approval is Definition 18's singleton case (Remark 3.9's vacuity), not a tie;
* for the properly mixed label `(½, ½)`, `A_d^+ = {a, b}` and both values are `10`: the genuine
  limit tie of 2-053, which D2 breaks (`limitTie_eventTremble_b_zero`).

So the 2-053 content of `limitTie_routes_differ` is carried by the mixed labels; `δ_b`'s
D1-approval is the Remark 3.9 phenomenon the package already exhibits on `fiveTen`. Not
imported by the library.
-/

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Catalogue

/-- Under `δ_b` at `d`, `a` is subjectively impossible at the limit state: `A_d^+ = {b}`. -/
theorem probe_limitTie_pureB_aPlus :
    APlus (fun _ => ltState (FinDistr.pure .b)) ltActEv .d = {Act2.b} := by
  ext x
  simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [ltState_pr, limitTie_nu]
  cases x <;> simp [ltActEv, procLT, FinDistr.pure_w]

/-- Under the fair mixture at `d`, both acts are subjectively possible: `A_d^+ = {a, b}`. -/
theorem probe_limitTie_fair_aPlus :
    APlus (fun _ => ltState (procQ (1/2) (by norm_num) (by norm_num) ())) ltActEv .d = Finset.univ := by
  ext x
  simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  rw [ltState_pr, limitTie_nu]
  cases x <;> simp [ltActEv, procLT, procQ] <;> norm_num

/-- Under the fair mixture, the two limit-state act values at `d` are both `10`: a genuine tie. -/
theorem probe_limitTie_fair_tie :
    (ltState (procQ (1/2) (by norm_num) (by norm_num) ())).V (ltActEv .d .a) = 10 ∧
    (ltState (procQ (1/2) (by norm_num) (by norm_num) ())).V (ltActEv .d .b) = 10 := by
  constructor <;>
    (rw [ltState, calibratedState_V, Finset.inter_univ, limitTie_paySum, limitTie_nu];
     simp [ltActEv, procLT, procQ]; norm_num)

end Cleanroom.Decision.DpCalibration
