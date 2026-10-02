import Cleanroom.Decision.DpFaithfulUdt.Mugging

/-!
# Audit r2 (adversarial) probe: F15 in its strongest form

F15 (`payCf_cudt_pays`) exhibits one success-obeying supposition supported on the realized atom
`(T,pay,0)` under which act-event cUDT pays (`V = 1` there). This probe shows the supposed value is
*completely* free: for every `c : ℚ` there is a `cf` obeying v2 Definition 2's success axiom,
supported at the pay event on `(T,pay,0)` alone, with `V^{pay}(pay) = c`. So "success + support on
realized atoms" determines nothing about `V^{pay}(pay)`, and the inference in FA-7′(ii′) needs
either rigid atom values or the payoff clause of counterfactual calibration — exactly as
`mug1_actEvent_cudt_refuses` assumes. Not imported by the library.
-/

namespace Cleanroom.Decision.DpFaithfulUdt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration

/-- A success-obeying supposition, supported on `(T,pay,0)` at the pay event, with any value. -/
theorem success_support_free_value (c : ℚ) :
    ∃ cf : Cf MugW ℚ, Success cf ∧ (cf (mugActEv () .a)).pr {MugW.tPay} = 1 ∧
      (cf (mugActEv () .a)).V (mugActEv () .a) = c := by
  refine ⟨fun X => if h : X.Nonempty then State.ofConst (uniformOn X h) c else State.trivial,
    ?_, ?_, ?_⟩
  · intro X hX
    simp only [dif_pos hX]
    exact probOf_uniformOn_self X hX
  · show (if h : ({MugW.tPay} : Finset MugW).Nonempty then
        State.ofConst (uniformOn {MugW.tPay} h) c else State.trivial).pr {MugW.tPay} = 1
    rw [dif_pos (Finset.singleton_nonempty _)]
    exact probOf_uniformOn_self _ (Finset.singleton_nonempty _)
  · show (if h : ({MugW.tPay} : Finset MugW).Nonempty then
        State.ofConst (uniformOn {MugW.tPay} h) c else State.trivial).V {MugW.tPay} = c
    rw [dif_pos (Finset.singleton_nonempty _)]
    simp

end Cleanroom.Decision.DpFaithfulUdt

#print axioms Cleanroom.Decision.DpFaithfulUdt.success_support_free_value
