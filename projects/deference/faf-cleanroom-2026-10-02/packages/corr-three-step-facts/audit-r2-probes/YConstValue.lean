import Cleanroom.Corrigibility.CorrThreeStepFacts.CommonPrior

/-!
# Audit r2 (adversarial) probe — `twoOptionValueY` with a constant `y` is the parent's `twoOptionValue`

The docstring of `twoOptionValueY` claims "with `yOf` constant this is the parent's
`twoOptionValue`" without a declaration. One line closes it; the new definition of record is
anchored to the parent's. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrThreeStepFacts.AuditR2

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect
open Cleanroom.Corrigibility.CorrThreeStepFacts

/-- With `yOf` constant the `y`-informed two-option value is the parent's `twoOptionValue`. -/
theorem twoOptionValueY_const_y {W A₁ A₂ : Type*} [Fintype W] [Fintype A₂] [DecidableEq A₂]
    (S : ThreeStep W A₁ A₂) (a : A₁) (c s : A₂) :
    twoOptionValueY S a (fun _ => ()) c s = S.twoOptionValue a c s := by
  unfold twoOptionValueY twoOptionValue
  rw [Fintype.sum_unique]
  have hc : cell (fun _ : W => ()) () = univ := by ext w; simp [cell]
  rw [hc]
  simp only [pressExpectOn, silentExpectOn, obsExpect, obsWeight_press, obsWeight_silent]

end Cleanroom.Corrigibility.CorrThreeStepFacts.AuditR2
