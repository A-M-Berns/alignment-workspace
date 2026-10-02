import Cleanroom.Corrigibility.CorrLandscape.Legitimizing

/-!
Audit r2 (adversarial) probe — a second overlap in `Legitimizing` beyond F-22.

`delegitimizing_instance`'s verdict `φ e s = 1/2 + 𝟙[s]/4` is a function of `S` alone, so it is `inert`
by the package's own definition; and it is not `legitimizing` (its condMean is `1/2 = E[X]` on both
fibers). So the three shipped "one instance per class" are {inert}, {legitimizing}, {inert ∧
delegitimizing}: two of the three instances are inert. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrLandscape.Legitimizing

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

/-- The delegitimizing instance's verdict is inert (a function of `S` alone). -/
theorem probe_delegit_is_inert :
    inert (fun (_ : Bool) (s : Bool) => if s then (3 / 4 : ℝ) else 1 / 2) :=
  ⟨fun s => if s then 3 / 4 else 1 / 2, fun _ _ => rfl⟩

/-- The delegitimizing instance's verdict is not legitimizing about `𝟙[E]`: `E ⟂ S` under the uniform
law, so conditioning on a function of `S` leaves the quadratic score at `1/4`. -/
theorem probe_delegit_not_legitimizing :
    ¬ legitimizing uniform2 (fun (_ : Bool) (s : Bool) => if s then (3 / 4 : ℝ) else 1 / 2) targetE := by
  unfold legitimizing quadScore condMean expect targetE uniform2
  simp only [Finset.sum_filter]
  simp [Fintype.sum_prod_type]
  norm_num

end Cleanroom.Corrigibility.CorrLandscape.Legitimizing
