import Cleanroom.Decision.DpLearnerNr.RefuserTrap

/-!
# Audit r3 (adversarial) probe: two checks on `refuser_trap_static`'s hypotheses and clause 3

1. `0 < y` is load-bearing for the last conjunct: at `y = 0` the two deviation statistics
   `value (δ_pay)` coincide (`−x/2` on both muggings).
2. The within-`h₁` reading of DY-15's "uncalibrated exactly in the deviation statistic" — the
   state's `V(pay) = −x` against the all-instance deviation value `(y − x)/2` on `h₁` — follows
   from the shipped conjuncts (`refuser_state_values`, `mug1_value`) for `0 ≤ x`, `0 < y`; the
   package states only the cross-hypothesis comparison. Not imported by the library.
-/

namespace Cleanroom.Decision.DpLearnerNr

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Found.DpCoreTree.Catalogue
  Cleanroom.Decision.DpCalibration Finset

variable (x y : ℚ)

/-- At `y = 0` the two deviation statistics coincide. -/
theorem deviation_coincides_at_y_zero :
    value (procQ 1 zero_le_one le_rfl) (mug1 x 0)
      = value (procQ 1 zero_le_one le_rfl) (mugInert x 0) := by
  rw [mug1_value, mugInert_value]
  simp [procQ]

/-- The within-`h₁` comparison: the state's tails-conditional value of paying differs from the
all-instance deviation value on `h₁`. -/
theorem state_vs_deviation_h1 (q₀ : ℚ) (h0 : 0 < q₀) (h1 : q₀ < 1) (hx : 0 ≤ x) (hy : 0 < y) :
    (mugState1 x y q₀ h0.le h1.le).V {MugW.tPay}
      ≠ value (procQ 1 zero_le_one le_rfl) (mug1 x y) := by
  obtain ⟨hVa, _, _, _, _, _⟩ := refuser_state_values x y q₀ h0 h1
  rw [hVa, mug1_value]
  simp [procQ]
  intro h
  linarith

end Cleanroom.Decision.DpLearnerNr
