import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith

/-! Load-bearing scalar algebra for the joint movement argument. -/

namespace NormativeLearner

def posPart (x : ℚ) : ℚ := max 0 x

/-- A compiler jump is a difference of two prefix payoffs.  A common lower
risk limit and upper cap therefore bound its adverse and absolute scalar sizes. -/
theorem compilerJumpCap
    {R L gOld gNew : ℚ}
    (hOldLower : -R ≤ gOld) (hNewLower : -R ≤ gNew)
    (hOldUpper : gOld ≤ L) (hNewUpper : gNew ≤ L) :
    posPart (gNew - gOld) ≤ L + R ∧ |gNew - gOld| ≤ L + R := by
  constructor
  · unfold posPart
    apply max_le
    · linarith
    · linarith
  · rw [abs_le]
    constructor <;> linarith

/-- Recursive total-movement majorant.  The equivalent coefficients are
`1+kappa=1/theta` and `epsilonSum/theta+(kappa+1)R=(epsilonSum+R)/theta`. -/
def movementCap (theta epsilonSum R ordinary : ℚ) : ℕ → ℚ
  | 0 => ordinary
  | n + 1 => (1 / theta) * movementCap theta epsilonSum R ordinary n + (epsilonSum + R) / theta

/-- Any sequence obeying the one-jump recurrence stays below `movementCap`. -/
theorem movementCap_induction
    {theta epsilonSum R ordinary : ℚ}
    (ha : 0 < theta)
    (actual : ℕ → ℚ)
    (hzero : actual 0 ≤ ordinary)
    (hstep : ∀ n, actual (n + 1) ≤
      (1 / theta) * actual n + (epsilonSum + R) / theta) :
    ∀ n, actual n ≤ movementCap theta epsilonSum R ordinary n := by
  intro n
  induction n with
  | zero => simpa [movementCap] using hzero
  | succ n ih =>
      rw [movementCap]
      have hcoef : 0 ≤ (1 / theta) :=
        div_nonneg (by norm_num) (le_of_lt ha)
      have hmul := mul_le_mul_of_nonneg_left ih hcoef
      have hadd := add_le_add_right hmul ((epsilonSum + R) / theta)
      exact (hstep n).trans (by simpa [add_comm] using hadd)

end NormativeLearner
