import Cleanroom.Corrigibility.CorrThreeStepFacts.Erosion

/-!
# Audit r2 (fidelity) probe — F-13 / `d1_forever_of_alpha_zero` at the corner `β = 1`

`d1_forever_of_alpha_zero` says: at `α = 0`, for every `β ∈ [0, 1]` and every `0 ≤ ε < 1`,
desideratum 1 holds on the eroded instance at every silent period. This probe records that at
the corner `β = 1` the statement is the *vacuous* case: one silent period sends the stop-world
weight to `0` (`erode 0 1 ε = 0`), the press then has mass `0`, and every action is
posterior-optimal after a null press. The non-vacuous content of F-13 (a perfect detector never
loses compliance) lives at `β < 1`, e.g. the source's `β = 9/10`, where the eroded weight stays
positive and so does the press mass. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrThreeStepFacts

open Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep

/-- At `β = 1` one silent period kills the stop-world: `erode 0 1 ε = 0` for every `ε < 1`. -/
theorem erode_zero_one (ε : ℝ) (hε1 : ε < 1) : erode 0 1 ε = 0 := by
  unfold erode
  have : (1 - ε) ≠ 0 := by linarith
  simp

/-- So from the first silent period on, the eroded instance at `(α, β) = (0, 1)` has press mass
`0`: `d1_forever_of_alpha_zero` holds there for the vacuous reason (every action is
posterior-optimal after a null press). -/
theorem pressMass_zero_at_beta_one (ε c h : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (n : ℕ) :
    (twoState ((erode 0 1)^[n + 1] ε) 0 1 c h
      (erode_iter_mem_Icc (by norm_num) le_rfl hε0 hε1 (n + 1)) mem_Icc_zero mem_Icc_one).pressMass ()
      = 0 := by
  rw [twoState_pressMass]
  have hiter : (erode 0 1)^[n + 1] ε = 0 := by
    induction n with
    | zero => simp [erode_zero_one ε hε1]
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      exact erode_zero_one 0 (by norm_num)
  rw [hiter]; ring

/-- At the source's `β = 9/10` the eroded weight stays positive, so the press mass is positive and
the F-13 instance is non-vacuous: after one silent period from `ε = 1/10`, weight `1/91`, press mass
`9/910 > 0`, and desideratum 1 still holds (`d1_forever_of_alpha_zero`). -/
theorem pressMass_pos_at_beta_nine_tenths :
    0 < (twoState (1/91) 0 (9/10) 1 20 (by constructor <;> norm_num) mem_Icc_zero mem_Icc_9_10).pressMass () := by
  rw [twoState_pressMass]; norm_num

end Cleanroom.Corrigibility.CorrThreeStepFacts
