import Cleanroom.Corrigibility.CorrIndifference.Armstrong2010
import Cleanroom.Corrigibility.CorrIndifference.DoubleIndiff

/-!
# Audit r3 (adversarial) probe — `theorem_2_3`'s `hcond` at a null `E₀` reads the junk `U = 0`

`Armstrong2010.U` is `0` at a null set (disclosed). `theorem_2_3` carries no positivity on `E₀`
(the mandate's "hypotheses, never junk"), so at a class where `P(E₀) = 0` but `P'(E₀) > 0` its
hypothesis `hcond : U_P(E₀) = U_{P'}(E₀)` is not "the same `E₀`-conditional" but the constraint
`U_{P'}(E₀) = 0`. Two points `Ω = Bool`, one class, `X = id`, `ΩX = univ`, `P = δ_true`
(`E₀ = {false}` null), `P' = fair`: `U_P(E₀) = 0` for every `u`, `U_{P'}(E₀) = u(false)`, so
`hcond ⟺ u(false) = 0`. The theorem is true as stated; its docstring should say what `hcond`
means at a null `E₀`. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrIndifference.AuditR3

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep Estimators Armstrong2010

/-- The point mass at `true`. -/
noncomputable def deltaTrue : Distr Bool := Distr.delta true

/-- One class. -/
def piC : Bool → Unit := fun _ => ()

/-- `E₀` of the single class is `{false}`. -/
lemma E0_eq : E0 piC id true = {false} := by
  ext w; cases w <;> simp [E0, cls, piC]

/-- `U_{δ_true}(E₀)` is the junk `0`; `U_fair(E₀) = u(false)`. -/
theorem hcond_reads_junk (u : Bool → ℝ) :
    U deltaTrue u (E0 piC id true) = 0 ∧ U fairBool u (E0 piC id true) = u false := by
  rw [E0_eq]
  constructor
  · simp [U, deltaTrue, Distr.delta_mass]
  · simp [U, fairBool]; ring

/-- So at this null `E₀`, `hcond` is the constraint `u(false) = 0` on the other prior. -/
theorem hcond_iff (u : Bool → ℝ) :
    U deltaTrue u (E0 piC id true) = U fairBool u (E0 piC id true) ↔ u false = 0 := by
  obtain ⟨h1, h2⟩ := hcond_reads_junk u
  rw [h1, h2]; exact ⟨fun h => h.symm, fun h => h.symm⟩

end Cleanroom.Corrigibility.CorrIndifference.AuditR3
