import Cleanroom.Corrigibility.CorrLandscape.Erosion

/-!
Audit r2 (adversarial) probe — `Erosion.switch_iff_refuted` under the *weak* reading of "wins".

The library refutes wentworth-judge's "C-row wins iff `δ < (1−λ)c/(c+h)`" with "wins" read as strict
improvement (at `λ = 7/10` no rule beats absolute). This probe closes the other reading: with "wins" read
as "every covered conditioned rule is at least as good as absolute", the "if" direction also fails —
at `δ = 1/100 < 3/50` there is a covered credence (`π̂(0) = 7/34 − 1/100 < q`) whose conditioned rule is
*strictly worse* than absolute (`31/100 > 30/100`). Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrLandscape.Erosion

open FactoredSpaces Cleanroom.Found.CorrThreeStep Map Trichotomy
open Finset hiding expect

/-- A credence covered at tolerance `1/100` on `toySeven` that resists at `s = 0`. -/
noncomputable def probeCred : Bool → ℝ := fun s => if s then 21 / 22 else 333 / 1700

theorem probe_weak_reading_refuted :
    (1 / 100 : ℝ) < (1 - 7 / 10) * 1 / (1 + 4) ∧
      covered probeCred toySeven (1 / 100) ∧
      loss toySeven absoluteRule 1 4 0 < loss toySeven (conditionedRule probeCred 0 1 4) 1 4 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := toySeven_mass
  refine ⟨by norm_num, ?_, ?_⟩
  · intro s _
    cases s
    · simp only [probeCred, Bool.false_eq_true, ↓reduceIte, piStar, sigMass, h2, h4]
      rw [abs_le]; constructor <;> norm_num
    · simp only [probeCred, ↓reduceIte, piStar, sigMass, h1, h3]
      rw [abs_le]; constructor <;> norm_num
  · have hb0 : conditionedRule probeCred 0 1 4 false = true := by
      simp [conditionedRule, probeCred, qk]; norm_num
    have hb1 : conditionedRule probeCred 0 1 4 true = false := by
      simp [conditionedRule, probeCred, qk]; norm_num
    rw [loss_absolute]
    simp [loss, Fintype.sum_bool, hb0, hb1, cost, sigMass, lam, h1, h2, h3, h4]
    norm_num

end Cleanroom.Corrigibility.CorrLandscape.Erosion
