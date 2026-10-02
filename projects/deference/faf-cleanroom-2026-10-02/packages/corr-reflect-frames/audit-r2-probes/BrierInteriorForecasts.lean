import Cleanroom.Corrigibility.CorrReflectFrames.WitnessesD

/-!
Audit r2 (adversarial) probe — the shipped N+ for `brier_expLoss_le_constLoss`
(`frame4_brier_strict`, `φ = {0, 1}` = branch `A`) is degenerate: the expert forecasts `φ`
perfectly (announcements `1` and `0`), so its Brier loss is `0`. This probe gives the same
frame with `φ = {0, 2}` (one atom per branch): forecasts `2/3` and `1/4`, both interior,
value-form reflection holds (refinement), and the Brier improvement is strict but not to zero,
`59/288 < 143/576`. Grades the shipped witness N+ (it inhabits the full package with a strict
inequality) but notes a sharper one exists. Nothing here is imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames.AuditR2

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames
  Cleanroom.Corrigibility.CorrReflectFrames.Witnesses

noncomputable section

abbrev φAB : Finset (Fin 4) := {0, 2}

theorem frame4_brier_interior :
    ValueReflectsOn π4 frame4 φAB ∧
      mass (frame4.P 0) φAB = 2 / 3 ∧ mass (frame4.P 2) φAB = 1 / 4 ∧
      expLoss π4 frame4 φAB brier = 59 / 288 ∧ constLoss π4 φAB brier = 143 / 576 ∧
      (59 / 288 : ℝ) < 143 / 576 := by
  obtain ⟨hr0, hr2⟩ := frame4_rows
  obtain ⟨hr1, hr3⟩ := frame4_rows'
  refine ⟨valueReflects_iff_forall_on.1 (refineFrame_valueReflects _ _) _, ?_, ?_, ?_, ?_,
    by norm_num⟩
  · rw [hr0, mass, sum_pair (show (0 : Fin 4) ≠ 2 by decide)]; simp
  · rw [hr2, mass, sum_pair (show (0 : Fin 4) ≠ 2 by decide)]; simp
  · simp only [expLoss, Fin.sum_univ_four, hr1, hr3, hr0, hr2, brier, ind, mass,
      sum_pair (show (0 : Fin 4) ≠ 2 by decide)]
    simp [π4]
    norm_num
  · simp only [constLoss, Fin.sum_univ_four, brier, ind, mass,
      sum_pair (show (0 : Fin 4) ≠ 2 by decide)]
    simp [π4]; norm_num

end

end Cleanroom.Corrigibility.CorrReflectFrames.AuditR2
