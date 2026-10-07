import Cleanroom.Corrigibility.CorrValueChange.Fine
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
Audit r4 (fidelity) probe for `corr-value-change`, Claim 4's equality clause (§2.4).

The note: "Equality holds iff the modification carries no information about `u_{θ,a}`." The
library proves the equality case as "iff `Ū^{(i)}_a = Ū_a` on the support" (`msErr_eq_iff`,
`representation_eq_iff`) and labels it a variant. This probe shows the note's sentence is false in
its "only if" direction under the natural reading of "carries no information" (independence of the
outcome from `u_{θ,a}`): a reflected modification whose outcome is *informative* about `u_{θ,a}`
(it tells the agent whether `u = 0` or `u = ±1`) leaves the conditional mean unchanged, so the
mean-square error is unchanged (`1/2 = 1/2`). Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open Finset

noncomputable section

/-- The joint `P(((), θ), i)`: outcome `true` (mass `1/2`) is `θ = 1`; outcome `false` (mass `1/2`)
is `θ = 0` or `θ = 2`, `1/4` each. -/
def c4Joint : Joint (Unit × Fin 3) Bool where
  P := fun x i => if i then ![0, 1 / 2, 0] x.2 else ![1 / 4, 0, 1 / 4] x.2
  nonneg := fun x i => by
    rcases x with ⟨_, θ⟩
    cases i <;> fin_cases θ <;> simp <;> norm_num
  sum_one := by
    simp [Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_three, Fintype.sum_bool]
    norm_num

/-- The installed states: the conditionals `Q_true = δ_1`, `Q_false = (1/2, 0, 1/2)`. -/
def c4Installed : Installed (Unit × Fin 3) Bool where
  Q := fun i x => if i then ![0, 1, 0] x.2 else ![1 / 2, 0, 1 / 2] x.2
  nonneg := fun i x => by
    rcases x with ⟨_, θ⟩
    cases i <;> fin_cases θ <;> simp <;> norm_num
  sum_one := fun i => by
    cases i <;> simp [Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_three] <;> norm_num

/-- One act; the candidate values `u_θ = (-1, 0, 1)`. -/
def c4U : Fin 3 → Unit → Unit → ℝ := fun θ _ _ => ![-1, 0, 1] θ

theorem c4π (i : Bool) : c4Joint.π i = 1 / 2 := by
  cases i <;> simp [Joint.π, c4Joint, Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_three] <;>
    norm_num

/-- (R⁺) holds: the installed states are the conditionals. -/
theorem c4_reflection : Reflection c4Joint c4Installed := by
  intro i _ x
  rw [c4π]
  rcases x with ⟨_, θ⟩
  cases i <;> fin_cases θ <;> simp [c4Joint, c4Installed] <;> norm_num

/-- The outcome is informative about `u_{θ,a}`: `P(θ = 1 ∧ i = true) = 1/2 ≠ 1/4 = π_true · P⁺(θ = 1)`
(equivalently `P(u = 0 ∣ i = true) = 1 ≠ 1/2 = P(u = 0)`). -/
theorem c4_informative : c4Joint.P ((), 1) true ≠ c4Joint.π true * c4Joint.marg ((), 1) := by
  rw [c4π]
  simp [c4Joint, Joint.marg]

/-- Yet the mean-square error of the installed representation equals the current one: both `1/2`.
So the "only if" of "equality iff the modification carries no information about `u_{θ,a}`" fails
under the independence reading; what is true is `representation_eq_iff`'s clause. -/
theorem c4_equality :
    msErr c4Joint c4U () (fun ω i => installedEffU c4Installed c4U i () ω) = 1 / 2 ∧
    msErr c4Joint c4U () (fun ω _ => Ubar c4Joint c4U () ω) = 1 / 2 ∧
    msErr c4Joint c4U () (fun ω i => installedEffU c4Installed c4U i () ω) =
      msErr c4Joint c4U () (fun ω _ => Ubar c4Joint c4U () ω) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [msErr, installedEffU, Ubar, Pω, Pωi, c4Joint, c4Installed, c4U, Fintype.sum_prod_type,
      Fintype.sum_unique, Fin.sum_univ_three, Fintype.sum_bool] <;> norm_num

/-- The library's own equality clause instantiated: `representation_eq_iff` holds here on both
sides, under reflection. -/
theorem c4_eq_iff_instance :
    msErr c4Joint c4U () (fun ω i => installedEffU c4Installed c4U i () ω) =
      msErr c4Joint c4U () (fun ω _ => Ubar c4Joint c4U () ω) ↔
    ∀ ω i, 0 < Pωi c4Joint ω i → installedEffU c4Installed c4U i () ω = Ubar c4Joint c4U () ω :=
  representation_eq_iff c4_reflection c4U ()

end

end Cleanroom.Corrigibility.CorrValueChange
