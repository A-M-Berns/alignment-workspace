import Cleanroom.Corrigibility.CorrReflectFrames.WitnessesD

/-!
Audit r2 (fidelity) probe — the Brier witness of `brier_expLoss_le_constLoss`.

The shipped positive witness `Witnesses.frame4_brier_strict` (repair round 1) takes `φ = {0, 1}`,
which is branch `A` of `frame4`: the row on branch `A` announces `φ` at `1` and the row on branch
`B` at `0`, so the expert's forecast is the indicator itself and its Brier loss is `0`. The
inequality is inhabited at the perfect-information extreme (`frame4_brier_strict_announces_0_1`).
The same frame carries an interior instance: `φ = {0, 2}` (one atom from each branch) is
announced at `2/3` and `1/4`, value-form reflection holds (refinements are value-reflective),
and the expert's expected Brier loss `59/288` is strictly below the constant forecast's
`143/576` with both forecasts in `(0, 1)` — the conditional-variance content of the theorem is
exercised. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames.AuditR2

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames
  Cleanroom.Corrigibility.CorrReflectFrames.Witnesses

/-- The shipped witness's event `{0, 1}` is announced at `1` on branch `A` and `0` on branch `B`. -/
theorem frame4_brier_strict_announces_0_1 :
    mass (frame4.P 0) {0, 1} = 1 ∧ mass (frame4.P 2) {0, 1} = 0 := by
  obtain ⟨hr0, hr2⟩ := frame4_rows
  rw [hr0, hr2]
  constructor <;> (simp [mass, sum_pair (show (0 : Fin 4) ≠ 1 by decide)]; try norm_num)

/-- An interior Brier instance on `frame4`: `φ = {0, 2}`, forecasts `2/3` and `1/4`, value form
holds, `59/288 < 143/576`. -/
theorem brier_interior :
    ValueReflectsOn π4 frame4 {0, 2} ∧ expLoss π4 frame4 {0, 2} brier = 59 / 288 ∧
      constLoss π4 {0, 2} brier = 143 / 576 ∧ (59 / 288 : ℝ) < 143 / 576 ∧
      mass (frame4.P 0) {0, 2} = 2 / 3 ∧ mass (frame4.P 2) {0, 2} = 1 / 4 := by
  obtain ⟨hr0, hr2⟩ := frame4_rows
  obtain ⟨hr1, hr3⟩ := frame4_rows'
  refine ⟨valueReflects_iff_forall_on.1 (refineFrame_valueReflects _ _) _, ?_, ?_, by norm_num,
    ?_, ?_⟩
  · simp only [expLoss, Fin.sum_univ_four, hr1, hr3, hr0, hr2, brier, ind, mass,
      sum_pair (show (0 : Fin 4) ≠ 2 by decide)]
    simp [π4]
    norm_num
  · simp only [constLoss, Fin.sum_univ_four, brier, ind, mass,
      sum_pair (show (0 : Fin 4) ≠ 2 by decide)]
    simp [π4]
    norm_num
  · rw [hr0]
    simp [mass, sum_pair (show (0 : Fin 4) ≠ 2 by decide)]
  · rw [hr2]
    simp [mass, sum_pair (show (0 : Fin 4) ≠ 2 by decide)]

end Cleanroom.Corrigibility.CorrReflectFrames.AuditR2
