import Cleanroom.Corrigibility.CorrOsgChai.Cellwise

/-!
# Audit r2 (adversarial) probe — the cell-blind agent satisfies desideratum 1 on the File
Deletion Game

`fileDeletionTS.D1At ()`: in the aggregate (the agent not conditioning on its own code
observation) stopping is press-posterior-optimal, `E[V(cont) 1_Pr] = ¼(3 − 5) = −1/2 ≤ 0`.
Together with `cellL_not_d1At` this pins the scope of the T12 refutation row: reading (b) is
refuted *on a cell*; drop the observation slot ("on every cell") and the sentence survives this
very instance. The row states the cellwise reading, so this is a scope check, not a defect.
Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrOsgChai.AuditR2

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
  Cleanroom.Corrigibility.CorrOsgChai
open Finset hiding expect

/-- Desideratum 1 holds for the cell-blind agent on the File Deletion Game. -/
theorem fileDeletionTS_d1At_aggregate : fileDeletionTS.D1At () := by
  refine ⟨.stop, by simp [fileDeletionTS], fun b' => ?_⟩
  cases b' <;>
    simp only [obsExpect, obsWeight_press, fileDeletionTS, uniform_mass_fin2_fin2,
      Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    simp [fdUa] <;> norm_num

/-- And the press is a genuine event there: mass `1/2`. -/
theorem fileDeletionTS_pressMass : fileDeletionTS.pressMass () = 1 / 2 := by
  simp only [pressMass, fileDeletionTS, uniform_mass_fin2_fin2, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  simp
  norm_num

end Cleanroom.Corrigibility.CorrOsgChai.AuditR2
