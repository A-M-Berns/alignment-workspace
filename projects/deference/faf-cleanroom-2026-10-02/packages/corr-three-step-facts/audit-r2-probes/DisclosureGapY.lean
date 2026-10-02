import Cleanroom.Corrigibility.CorrThreeStepFacts.CommonPrior
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Audit r2 (adversarial) probe — T9 with `y` in hand: the repaired comparison is strict on a frame

The package's T9 rows ship no witness (the hypotheses are trivially satisfiable). This probe shows the
repaired, `y`-informed comparison `disclosure_prefers_disclose` is not an equality in general — the
theorem has bite. Six worlds, uniform, programmers' cells `A = {0, 1} | B = {2, 3} | C = {4, 5}`, the
agent's `y` = parity, `X = (−3, 1, 1, −3, 1, 1)`: `A` and `B` are both pressed (sums `−1/3`), `C` is
not; the keeping agent's information `(undisclosed press, y)` is worth `1/3`, while the disclosed press
(and hence `(h, y)`) is worth `2/3`. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrThreeStepFacts.AuditR2

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect
open Cleanroom.Corrigibility.CorrThreeStepFacts

/-- The uniform prior on six worlds. -/
noncomputable def unif6 : Distr (Fin 6) where
  mass _ := 1/6
  nonneg _ := by norm_num
  sum_eq_one := by simp

/-- The programmers' three cells `{0, 1} | {2, 3} | {4, 5}`. -/
def h6 : Fin 6 → Fin 3 := ![0, 0, 1, 1, 2, 2]

/-- The agent's `y`: parity. -/
def y6 : Fin 6 → Bool := fun i => decide (i.val % 2 = 0)

/-- The payoff `(−3, 1, 1, −3, 1, 1)`. -/
noncomputable def x6 : Fin 6 → ℝ := ![-3, 1, 1, -3, 1, 1]

/-- The keeping agent, holding `y`, is worth `1/3`: the pressed cells `A ∪ B` split by parity into
`{0, 2}` (sum `−1/3`) and `{1, 3}` (sum `−1/3`), both stopped; the unpressed `C` splits into `{4}`
and `{5}`, worth `1/6` each. -/
theorem keep_with_y_value : partValue2 unif6 x6 (undisclosedPressY unif6 h6 y6 x6) = 1/3 := by
  simp only [partValue2_eq, Fintype.sum_prod_type, Fintype.sum_bool]
  simp +decide [cellSumX, cell, sum_filter, Fin.sum_univ_succ, undisclosedPressY, undisclosedPress,
    signOf, h6, y6, unif6, x6] <;> norm_num

/-- The disclosed press is worth `2/3` (worlds `1, 2, 4, 5` continue). -/
theorem disclose_value : partValue2 unif6 x6 (disclosedPress unif6 h6 y6 x6) = 2/3 := by
  rw [partValue2_eq, Fintype.sum_bool]
  simp +decide [cellSumX, cell, sum_filter, Fin.sum_univ_succ, disclosedPress, signOf, hyOf, h6, y6,
    unif6, x6] <;> norm_num

/-- **The repaired T9(iii) is strict here**: `1/3 < 2/3` on the `y`-informed two-option value. -/
theorem disclose_strictly_better :
    twoOptionValueY (disclosure unif6 h6 y6 x6) false y6 .cont .stop <
      twoOptionValueY (disclosure unif6 h6 y6 x6) true y6 .cont .stop := by
  rw [twoOptionValueY_eq_partValue2_of_bool unif6 y6 x6 (disclosure unif6 h6 y6 x6) false
      (undisclosedPress unif6 h6 x6) (fun w => by simp [disclosure]) rfl (fun o => rfl),
    twoOptionValueY_eq_partValue2_of_bool unif6 y6 x6 (disclosure unif6 h6 y6 x6) true
      (disclosedPress unif6 h6 y6 x6) (fun w => by simp [disclosure]) rfl (fun o => rfl)]
  have e1 : (fun w => (undisclosedPress unif6 h6 x6 w, y6 w)) = undisclosedPressY unif6 h6 y6 x6 := rfl
  have e2 : (fun w => (disclosedPress unif6 h6 y6 x6 w, y6 w)) = disclosedPressY unif6 h6 y6 x6 := rfl
  rw [e1, e2, partValue2_disclosed_with_y, ← partValue2_disclosed, keep_with_y_value, disclose_value]
  norm_num

end Cleanroom.Corrigibility.CorrThreeStepFacts.AuditR2
