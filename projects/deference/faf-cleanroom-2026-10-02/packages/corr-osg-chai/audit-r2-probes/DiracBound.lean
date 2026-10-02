import Cleanroom.Corrigibility.CorrOsgChai.OffSwitch
import Mathlib.Tactic.FinCases

/-!
# Audit r2 (adversarial) probe — the `[0,1]` bound in `forall_osgDelta_delta_nonneg_iff` is
load-bearing

With `π^H ≡ 2` (outside `[0,1]`) and `U = ![1, 2] > 0`, every Dirac belief gives
`Δ = −U(1 − 2) = U ≥ 0`, yet `π^H ≠ rationalAllow U` where `U ≠ 0`. So the function-level
"iff H is rational" is false without the bound, as the theorem's `Hyps:` line says; the bound is
the paper's type of `π^H`, not a squeeze. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrOsgChai.AuditR2

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
  Cleanroom.Corrigibility.CorrOsgChai

/-- Without the bound the left side holds and the right side fails. -/
theorem forall_nonneg_without_bound :
    (∀ u₀ : Fin 2, 0 ≤ osgDelta (Distr.delta u₀) ![1, 2] (fun _ => (2 : ℝ))) ∧
      ¬ (∀ ω : Fin 2, (![1, 2] : Fin 2 → ℝ) ω ≠ 0 →
        (fun _ => (2 : ℝ)) ω = rationalAllow ![1, 2] ω) := by
  constructor
  · intro u₀
    rw [osgDelta_delta]
    fin_cases u₀ <;> simp <;> norm_num
  · intro h
    have := h 0 (by simp)
    simp [rationalAllow] at this

end Cleanroom.Corrigibility.CorrOsgChai.AuditR2
