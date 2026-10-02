import Cleanroom.Corrigibility.CorrPositionFinds.Assumptions

/-!
# Audit r3 (adversarial) probe — under reading (B) the *noise* channel `¬L` is "viable" too

F-8 (repair r2) says that under reading (B) — the reflection equation read for the
`L`-conditional model — §2.11's criterion is *vacuous* for every sensor-latent `L`. The package
proves the `L` side (`legitMix_posteriorPress_wrong_given_L`: the `L`-conditional press posterior
is the honest instance's) and asserts the vacuity in prose ("the tower identity in a conditional
model"). This probe makes the sharpest form numeric: the **`¬L`-conditional** press posterior on
the mixture equals the prior `ε` for every `q < 1`, `γ > 0`, `P(Pr) > 0` — so "reflection
conditional on `¬L`" holds by exactly the same construction as I5.3's "conditional on `L`", and
under (B) the criterion accepts the illegitimate channel (the press is noise) as readily as the
legitimate one. Cell at I5.3's parameters, `q = 1/4`: `P(wrong | Pr, ¬L) = 1/50 = ε`.
Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrPositionFinds.AuditR3

open Finset FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
  Cleanroom.Corrigibility.CorrPositionFinds

variable (ε α β c h γ q : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)

/-- `P(wrong, ¬L | Pr) = ε(1 − q)γ / P(Pr)` on the mixture. -/
lemma posteriorPress_wrong_off_L :
    (legitMix ε α β c h γ q hε hα hβ hγ hq).posteriorPress () (.wrong, false) =
      ε * (1 - q) * γ / (q * (ε * β + (1 - ε) * α) + (1 - q) * γ) := by
  simp only [posteriorPress, pressMass, Fintype.sum_prod_type, Fintype.sum_bool, World.sum_eq,
    legitMix, legitPrior, legitWeight, legitPress, twoPoint_right, twoPoint_wrong, twoPress]
  congr 1 <;> ring

/-- `P(right, ¬L | Pr) = (1 − ε)(1 − q)γ / P(Pr)` on the mixture. -/
lemma posteriorPress_right_off_L :
    (legitMix ε α β c h γ q hε hα hβ hγ hq).posteriorPress () (.right, false) =
      (1 - ε) * (1 - q) * γ / (q * (ε * β + (1 - ε) * α) + (1 - q) * γ) := by
  simp only [posteriorPress, pressMass, Fintype.sum_prod_type, Fintype.sum_bool, World.sum_eq,
    legitMix, legitPrior, legitWeight, legitPress, twoPoint_right, twoPoint_wrong, twoPress]
  congr 1 <;> ring

/-- **The `¬L`-conditional press posterior is the prior:** `P(wrong | Pr, ¬L) = ε` for every
`q < 1`, `γ > 0`, `P(Pr) > 0`. The noise channel's "reflection conditional on `¬L`" holds by the
same construction as I5.3's "conditional on `L`" — the `¬L`-model's posterior is the prior, and
the prior trivially reflects. Under reading (B) the criterion therefore accepts `¬L` too. -/
theorem noise_conditional_posterior_eq_prior (hq1 : q < 1) (hγ0 : 0 < γ)
    (hpm : 0 < q * (ε * β + (1 - ε) * α) + (1 - q) * γ) :
    (legitMix ε α β c h γ q hε hα hβ hγ hq).posteriorPress () (.wrong, false) /
        ((legitMix ε α β c h γ q hε hα hβ hγ hq).posteriorPress () (.wrong, false) +
          (legitMix ε α β c h γ q hε hα hβ hγ hq).posteriorPress () (.right, false)) = ε := by
  rw [posteriorPress_wrong_off_L, posteriorPress_right_off_L, ← add_div,
    div_div_div_cancel_right₀ hpm.ne']
  have hne : (1 - q) * γ ≠ 0 := (mul_pos (sub_pos.mpr hq1) hγ0).ne'
  have hden : ε * (1 - q) * γ + (1 - ε) * (1 - q) * γ = (1 - q) * γ := by ring
  rw [hden, div_eq_iff hne]
  ring

/-- The cell at I5.3's parameters, `q = 1/4` (where D1 fails): `P(wrong | Pr, ¬L) = 1/50 = ε`. -/
theorem noise_cell_quarter :
    (legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/4) mem_Icc_1_50 mem_Icc_1_20 mem_Icc_9_10
        mem_Icc_half mem_Icc_quarter).posteriorPress () (.wrong, false) /
      ((legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/4) mem_Icc_1_50 mem_Icc_1_20 mem_Icc_9_10
          mem_Icc_half mem_Icc_quarter).posteriorPress () (.wrong, false) +
        (legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/4) mem_Icc_1_50 mem_Icc_1_20 mem_Icc_9_10
          mem_Icc_half mem_Icc_quarter).posteriorPress () (.right, false)) = 1 / 50 :=
  noise_conditional_posterior_eq_prior _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)
    (by norm_num)

/-- And the same cell at `q = 1/2` (where D1 holds): the `¬L` side does not move with `q`. -/
theorem noise_cell_half :
    (legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/2) mem_Icc_1_50 mem_Icc_1_20 mem_Icc_9_10
        mem_Icc_half mem_Icc_half).posteriorPress () (.wrong, false) /
      ((legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/2) mem_Icc_1_50 mem_Icc_1_20 mem_Icc_9_10
          mem_Icc_half mem_Icc_half).posteriorPress () (.wrong, false) +
        (legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/2) mem_Icc_1_50 mem_Icc_1_20 mem_Icc_9_10
          mem_Icc_half mem_Icc_half).posteriorPress () (.right, false)) = 1 / 50 :=
  noise_conditional_posterior_eq_prior _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)
    (by norm_num)

end Cleanroom.Corrigibility.CorrPositionFinds.AuditR3
