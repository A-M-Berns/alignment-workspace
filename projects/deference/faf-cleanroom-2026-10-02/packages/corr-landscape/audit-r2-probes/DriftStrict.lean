import Cleanroom.Corrigibility.CorrLandscape.Drift

/-!
Audit r2 (adversarial) probe — `Drift.l1_nonexpansive` is not an identity: at the refutation cell `mCell`
the ℓ¹ deviation strictly decreases under one fresh-draw step (`141/275 < 6/11`), while the scalar
`|β − β_stat|` grows there (`beta_not_potential`). Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrLandscape.Drift

open Erosion Finset

theorem probe_l1_values :
    l1Dev mCell = 6 / 11 ∧ l1Dev (freshStep (1 / 10) mCell) = 141 / 275 := by
  constructor
  · simp only [l1Dev, mCell, mstat, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    simp (disch := norm_num) only [abs_of_nonneg, abs_of_nonpos]
    norm_num
  · simp only [l1Dev, freshStep, mCell, mstat, vis, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    simp (disch := norm_num) only [abs_of_nonneg, abs_of_nonpos]
    norm_num

theorem probe_l1_strict_at_mCell : l1Dev (freshStep (1 / 10) mCell) < l1Dev mCell := by
  obtain ⟨h1, h2⟩ := probe_l1_values
  rw [h1, h2]; norm_num

end Cleanroom.Corrigibility.CorrLandscape.Drift
