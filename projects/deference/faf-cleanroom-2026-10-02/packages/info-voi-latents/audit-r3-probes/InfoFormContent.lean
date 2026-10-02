import Cleanroom.Info.InfoVoiLatents.SplitInfoForm
import Cleanroom.Info.InfoVoiLatents.SplitWitness

/-!
# info-voi-latents — audit round 3 (adversarial) probe: `SplitInfoForm`'s conclusion has content

Probe file, not imported by the library. Elaborated with `scripts/lean-check`.

`SplitInfoForm.condMutualInfo_theta_signal_eq_zero_of_hval` proves `HVal k → I[θ : S | Λ ; joint μ k] = 0`.
Vacuity check: is the conclusion perhaps always `0` on `Bridge.joint` (which would make the
theorem say nothing)? No: at the θ-hole experiment (`Λ = Unit`, `θ = Fin 2` uniform, the signal
reveals `θ`; `¬ HVal revealθ` is `SplitWitness.hole_not_hval`),
`I[θ : S | Λ ; joint holePrior revealθ] = log 2`, computed through the package's own KL rendering
(`Eig.klFin_joint3_fact3_eq_condMutualInfo`) and the cell lemmas of `SplitInfoForm`.
-/

namespace AuditR3

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Info.InfoVoiLatents Cleanroom.Info.InfoVoiLatents.Voi
open Cleanroom.Info.InfoVoiLatents.Split Cleanroom.Info.InfoVoiLatents.Eig
open MeasureTheory ProbabilityTheory

noncomputable section

/-- The kernel of `revealθ`, as an equation (so the structure is never unfolded in place). -/
theorem revealθ_k (p : Unit × Fin 2) (s : Fin 2) : revealθ.k p s = if s = p.2 then 1 else 0 := rfl

/-- The `(S, Λ)`-marginal at the hole: `P(s, ()) = 1/2` for each signal (no `HVal` needed). -/
theorem pm2_sig_lam_hole (s : Fin 2) (u : Unit) :
    pm2 (Bridge.joint holePrior revealθ holePrior_mem) sigOf lamOf s u = 1 / 2 := by
  rw [← sum_pm3_x (Y := (sigOf : (Unit × Fin 2) × Fin 2 → Fin 2))
    (Z := (lamOf : (Unit × Fin 2) × Fin 2 → Unit)) measurable_thetaOf s u]
  simp_rw [pm3_joint holePrior_mem]
  fin_cases s <;> norm_num [holePrior, revealθ_k, Fin.sum_univ_two]

/-- `muΛ holePrior () = 1`. -/
theorem muΛ_hole (u : Unit) : muΛ holePrior u = 1 := by
  norm_num [muΛ, holePrior, Fin.sum_univ_two]

/-- **`I[θ : S | Λ] = log 2` at the θ-hole**: the information form is not automatic on the joint. -/
theorem hole_condMutualInfo :
    I[(thetaOf : (Unit × Fin 2) × Fin 2 → Fin 2) : (sigOf : (Unit × Fin 2) × Fin 2 → Fin 2)
      | (lamOf : (Unit × Fin 2) × Fin 2 → Unit) ; Bridge.joint holePrior revealθ holePrior_mem]
      = Real.log 2 := by
  rw [← klFin_joint3_fact3_eq_condMutualInfo measurable_thetaOf measurable_sigOf measurable_lamOf]
  unfold klFin
  rw [sum_prod3]
  simp only [joint3, fact3, pm3_joint holePrior_mem, pm2_theta_lam_joint holePrior_mem,
    pm1_lam_joint holePrior_mem, Fin.sum_univ_two, Fintype.sum_unique]
  simp only [pm2_sig_lam_hole, muΛ_hole]
  simp [holePrior, revealθ_k]
  norm_num <;> ring

/-- Hence `θ` and the signal are *not* conditionally independent given `Λ` at the hole. -/
theorem hole_not_condIndep :
    ¬ CondIndepFun (thetaOf : (Unit × Fin 2) × Fin 2 → Fin 2) (sigOf : (Unit × Fin 2) × Fin 2 → Fin 2)
      (lamOf : (Unit × Fin 2) × Fin 2 → Unit) (Bridge.joint holePrior revealθ holePrior_mem) := by
  intro h
  have := (ShannonInformation.condMutualInfo_eq_zero measurable_thetaOf measurable_sigOf
    measurable_lamOf).2 h
  rw [hole_condMutualInfo] at this
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne' this

/-- Together with `hole_not_hval`: an experiment failing `HVal` at which the information form
also fails — the theorem's antecedent and conclusion both bite. -/
theorem hole_both_fail : ¬ HVal revealθ ∧
    I[(thetaOf : (Unit × Fin 2) × Fin 2 → Fin 2) : (sigOf : (Unit × Fin 2) × Fin 2 → Fin 2)
      | (lamOf : (Unit × Fin 2) × Fin 2 → Unit) ; Bridge.joint holePrior revealθ holePrior_mem]
      ≠ 0 :=
  ⟨hole_not_hval, by rw [hole_condMutualInfo]; exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'⟩

end

end AuditR3
