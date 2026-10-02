import Cleanroom.Corrigibility.CorrOsgChai.Carey

/-!
# Audit r2 (adversarial) probe — the `ε`-range in `robot_R1_obeys` is load-bearing

At `ε = 1/20` (above the `1/26` threshold the docstring names, below the paper's `1/100`
bound's complement) the `R₁` robot *disobeys* the order `a`: its score for `a` after order `a` is
`1 − 13ε = 7/20 < 1/2`, so it plays `a'`. So `robot_R1_obeys` is not true for every `ε` and its
hypothesis `ε < 1/100` does work; and the derived robot behaviour in `fig1_value_le` is
sensitive to the noise model, not a constant. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrOsgChai.AuditR2

open Cleanroom.Corrigibility.CorrOsgChai

/-- At `ε = 1/20` the `R₁` robot disobeys the order `a`. -/
theorem robot_R1_disobeys_at_twentieth : robot (1 / 20) .R1 .act = .alt := by
  simp [robot, score, lik, optimalMove, rewardR, rewardTrue, Fin.sum_univ_two]
  norm_num

end Cleanroom.Corrigibility.CorrOsgChai.AuditR2
