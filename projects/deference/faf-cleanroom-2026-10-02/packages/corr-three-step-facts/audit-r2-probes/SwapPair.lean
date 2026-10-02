import Cleanroom.Corrigibility.CorrThreeStepFacts.WitnessesB
import Cleanroom.Corrigibility.CorrThreeStepFacts.Partition

/-!
# Audit r2 (adversarial) probe — T6(iii): a live full-package witness in the left disjunct

The ledger says of `constPair` that landing in the inert disjunct is "the best a full-package witness
can be, by the theorem's own content". It is not: the theorem's conclusion is a *disjunction*, and a
full-package pair with **equal press masses and a live channel** exists — two different sensors that
are permutations of each other over two worlds with equal prior mass and equal payoff. On `unif3` with
`X = (1, 1, −20)`, `press true = (1/20, 1/10, 9/10)` and `press false = (1/10, 1/20, 9/10)`: both
nondegenerate, equal press conditionals (`−17`), equal silence conditionals (`−1/13`), equal press
masses (`7/20`), sensors differing at world `0`, and the channel live (`−17 ≠ −1/13`). So the full
hypothesis package is inhabited by a non-inert, non-identical pair; the conclusion is then the
left disjunct, non-trivially. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrThreeStepFacts.AuditR2

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect
open Cleanroom.Corrigibility.CorrThreeStepFacts

/-- The payoff `(1, 1, −20)`. -/
noncomputable def X3 : Fin 3 → ℝ := ![1, 1, -20]

/-- Two sensors that swap worlds `0` and `1`. -/
noncomputable def swapPair : ThreeStep (Fin 3) Bool TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => unif3
  press := fun a => if a then ![1/20, 1/10, 9/10] else ![1/10, 1/20, 9/10]
  press_nonneg := fun a w => by cases a <;> fin_cases w <;> norm_num
  press_le_one := fun a w => by cases a <;> fin_cases w <;> norm_num
  V := fun _ _ => twoOptionV X3

/-- The full package of `pressMass_eq_or_condExp_eq` with a live channel and equal press masses. -/
theorem swapPair_full_package_live :
    swapPair.Nondegenerate true ∧ swapPair.Nondegenerate false ∧
      swapPair.condExpPress true X3 = swapPair.condExpPress false X3 ∧
      swapPair.condExpSilent true X3 = swapPair.condExpSilent false X3 ∧
      swapPair.pressMass true = swapPair.pressMass false ∧
      swapPair.press true 0 ≠ swapPair.press false 0 ∧
      swapPair.condExpPress true X3 ≠ swapPair.condExpSilent true X3 := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp [condExpPress, condExpSilent, obsExpect, pressMass, obsWeight_press, obsWeight_silent,
      Fin.sum_univ_three, swapPair, unif3, X3] <;> norm_num)

/-- The theorem applied to the pair lands in the left disjunct, with the right one false. -/
theorem swapPair_left_disjunct :
    swapPair.pressMass true = swapPair.pressMass false ∧
      ¬ swapPair.condExpPress true X3 = swapPair.condExpSilent true X3 := by
  obtain ⟨_, _, _, _, h5, _, h7⟩ := swapPair_full_package_live
  exact ⟨h5, h7⟩

end Cleanroom.Corrigibility.CorrThreeStepFacts.AuditR2
