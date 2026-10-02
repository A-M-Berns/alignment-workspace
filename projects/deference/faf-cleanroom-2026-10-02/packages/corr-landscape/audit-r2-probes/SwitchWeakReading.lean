import Cleanroom.Corrigibility.CorrLandscape.Erosion

/-!
# Audit round 2 (fidelity) probe — `Erosion.switch_iff_refuted` under the *weak* reading of "wins"

The ledger's refutation of the dialogue's "C-row wins iff `δ < (1−λ)c/(c+h)`" (wentworth-judge l. 101,
`judge_checks.py` (3)) reads "wins" as *strict* improvement and proves that at Toy T pause stakes with
`λ = 7/10` no rule at all beats absolute. Under the weak reading (`ℓ*(cond) ≤ ℓ*(absolute)`) the "iff"
also fails, but the library does not exhibit it: this probe does. A credence covered at `δ = 3/100`
(below the claimed bound `3/50`) — `π̂ = π* − 3/100` at both signals — resists at `s = 0`
(`7/34 − 3/100 < 1/5`) and pays `31/100 > 3/10 = ℓ*(absolute)`. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrLandscape.AuditR2

open FactoredSpaces Cleanroom.Found.CorrThreeStep Map Trichotomy Erosion
open Finset hiding expect

/-- The credence `π̂ = π* − 3/100` at both signals of `toySeven`. Source: audit probe. Kind: D. Fidelity: n/a -/
noncomputable def credWeak : Bool → ℝ := fun s => piStar toySeven s - 3 / 100

/-- Under the weak reading the dialogue's "iff" still fails at `λ = 7/10`: a covered credence at
`δ = 3/100 < 3/50` is strictly worse than absolute. Source: audit probe. Kind: N+. Fidelity: exact -/
theorem probe_weak_reading :
    covered credWeak toySeven (3 / 100) ∧
      loss toySeven (conditionedRule credWeak 0 1 4) 1 4 0 = 31 / 100 ∧
      loss toySeven absoluteRule 1 4 0 = 3 / 10 ∧
      (3 / 100 : ℝ) < (1 - 7 / 10) * 1 / (1 + 4) := by
  obtain ⟨h1, h2, h3, h4⟩ := toySeven_mass
  have hp0 : piStar toySeven false = 7 / 34 := by simp [piStar, sigMass, h2, h4]; norm_num
  have hp1 : piStar toySeven true = 21 / 22 := by simp [piStar, sigMass, h1, h3]; norm_num
  have hr0 : conditionedRule credWeak 0 1 4 false = true := by
    simp [conditionedRule, credWeak, qk, hp0]; norm_num
  have hr1 : conditionedRule credWeak 0 1 4 true = false := by
    simp [conditionedRule, credWeak, qk, hp1]; norm_num
  refine ⟨?_, ?_, ?_, by norm_num⟩
  · intro s _
    simp only [credWeak, sub_sub_cancel_left, abs_neg]
    norm_num
  · simp [loss, hr0, hr1, cost, h2, h3]
    norm_num
  · rw [loss_absolute]; simp [lam, h1, h2]; norm_num

end Cleanroom.Corrigibility.CorrLandscape.AuditR2
