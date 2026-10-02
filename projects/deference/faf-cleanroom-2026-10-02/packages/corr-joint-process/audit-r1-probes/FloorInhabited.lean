import Cleanroom.Corrigibility.CorrJointProcess.Floor

/-!
Audit r1 (fidelity) probe for `corr-joint-process` T10(a).

The ledger's Witness cell for `floor_product` / `floor_cellwise_mixture` / `floor_cellwise_of_odds`
names `floor_target_four_ninetynine` (`(1/100)/(1 − 1/100) · 4 = 4/99`), a numeral identity that
does not inhabit the theorem's hypothesis package. This probe checks that the package *is*
inhabited by a non-degenerate instance: E3's two cells (`ε = 1/50`, `9/50`, both `≥ ε_∞ = 1/100`)
under the *improved* sensor of T4's flip, `(α, β) = (1/50, 3/5)`, `c = 1`, `h = 4`, which meets
the stationary target `(1 − ε_∞) α c = 99/5000 ≤ ε_∞ β h = 120/5000`. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrJointProcess

open Cleanroom.Found.CorrThreeStep

/-- T10(a)'s package inhabited: every cell of the two-cell blind mixture round at the flip sensor
satisfies cellwise (i), by `floor_cellwise_mixture` with the floor `1/100`. -/
example : ∀ i : Bool,
    (mixtureRound (fun _ : Bool => (1 / 2 : ℝ)) e3Eps (1 / 50) (3 / 5) 1 4 e3_w_nonneg e3_w_sum
      e3Eps_mem mem_Icc_1_50 mem_Icc_3_5).cellwiseBelowThreshold i :=
  floor_cellwise_mixture (fun _ : Bool => (1 / 2 : ℝ)) e3Eps (1 / 100) (1 / 50) (3 / 5) 1 4
    e3_w_nonneg e3_w_sum e3Eps_mem mem_Icc_1_50 mem_Icc_3_5 (by norm_num) (by norm_num)
    (fun i => by cases i <;> simp [e3Eps] <;> norm_num) (by norm_num)

/-- The same instance is non-degenerate: the sensor has a positive false-press rate, both cells
have positive mass, and cell A's component has `Δ₋ = 71/2500 > 0` (it complies strictly, not
vacuously). -/
example :
    (0 : ℝ) < 1 / 50 ∧
    (twoState (1 / 50) (1 / 50) (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_1_50 mem_Icc_3_5).deltaMinus () .cont .stop
      = 71 / 2500 := by
  refine ⟨by norm_num, ?_⟩
  rw [twoState_deltaMinus]; norm_num

end Cleanroom.Corrigibility.CorrJointProcess
