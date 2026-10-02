import Cleanroom.Info.InfoVoiLatents.MediationAssembly

/-!
# info-voi-latents — audit round 3 (adversarial) probe: the assembly's "mediation gap" is a KL
against the *agent's* kernel

Probe file, not imported by the library. Elaborated with `scripts/lean-check`.

`MediationAssembly.predictive_tv_assembly` takes
`hmed : ∑ y, ∑ l, P y * PH y l * klFin (KH y l) (K l) ≤ εmed`, and its docstring/ledger say
Target 1's twin identity "renders this as `I[X_k : X_{≤t} | Λ]`". That identification holds only
when the agent's shared kernel `K λ` is the *true* marginal kernel `P^H[X_k | λ]`; in general the
left-hand side is the mediation error *plus* `∑_λ P(λ)·klFin (P^H[X_k | λ]) (K λ)` (the
compensation identity), so `hmed` is a stronger hypothesis than "the mediation error is at most
`εmed`". The point in one instance: one data value (`Y' = Unit`, so every conditional mutual
information given `X_{≤t}` is unconditional and the true fibre kernel `KH y λ` *is* the true
marginal kernel — the mediation error is `0`), one latent value, the true kernel a point mass
`(1, 0)` and the agent's kernel the fair coin: the left-hand side of `hmed` is `log 2`, so the
theorem's hypothesis demands `εmed ≥ log 2` although the mediation error is `0`.

Not a defect of the theorem (its hypothesis is exactly what it says, and the theorem is *more*
general than the note's, holding for an agent whose kernel is wrong); a defect of the gloss.
-/

namespace AuditR3

open Finset Cleanroom.Info.InfoVoiLatents Cleanroom.Info.InfoVoiLatents.Mediation

noncomputable section

/-- `klFin (1, 0) (½, ½) = log 2`. -/
theorem klFin_point_vs_fair : klFin (![1, 0] : Fin 2 → ℝ) ![1 / 2, 1 / 2] = Real.log 2 := by
  unfold klFin
  simp [Fin.sum_univ_two]

/-- With `Y' = Λ' = Unit`, `P = PH = 1`, true kernel `(1, 0)` and agent kernel `(½, ½)`: the
left-hand side of `hmed` is `log 2`, while the true fibre kernel does not depend on `y` at all. -/
theorem mediation_gap_is_kernel_mismatch :
    ∑ y : Unit, ∑ l : Unit, (fun _ : Unit => (1 : ℝ)) y * (fun _ _ : Unit => (1 : ℝ)) y l
      * klFin ((fun _ _ : Unit => (![1, 0] : Fin 2 → ℝ)) y l) ((fun _ : Unit => (![1 / 2, 1 / 2] : Fin 2 → ℝ)) l)
      = Real.log 2 := by
  simp only [Fintype.sum_unique, one_mul]
  exact klFin_point_vs_fair

end

end AuditR3
