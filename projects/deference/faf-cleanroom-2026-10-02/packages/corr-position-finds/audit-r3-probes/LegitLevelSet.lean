import Cleanroom.Corrigibility.CorrPositionFinds.Assumptions

/-!
# Audit round 3 (fidelity) probe: reading (A) of §2.11's equation on `legitMix` is the press-branch test

`Assumptions.legitMix_reflection_on_L_fails` states reading (A) as the *press-branch* inequality
`P(wrong | Pr, L) ≠ P(wrong | Pr)`. §2.11's equation is `P_{t₁}(φ | P_{t₂}(φ) = c, L) = c`, whose
conditioning event is the *level set* `{o : P(wrong | o) = c}`. The level set at `c = P(wrong | Pr)`
is exactly `{Pr}` only if the mixture's silence posterior differs from its press posterior. This
probe checks that at I5.3's parameters (`q = 1/2` and `q = 1/4`) it does — so the theorem's
press-branch test *is* the equation at that level, not a proxy for it — and, in general, that the
mixture press is informative about `ω` exactly when `α ≠ β` (given `0 < q`, `0 < ε < 1`), which is
the theorem's own hypothesis. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrPositionFinds.AuditR3

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
  Cleanroom.Corrigibility.CorrPositionFinds

/-- The mixture's silence posterior on `wrong` at `q = 1/2`: `12/1433`, not `4/81`. -/
theorem lm_half_silence_posterior :
    posteriorSilent (legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/2) mem_Icc_1_50 mem_Icc_1_20
        mem_Icc_9_10 mem_Icc_half mem_Icc_half) () (.wrong, true) +
      posteriorSilent (legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/2) mem_Icc_1_50 mem_Icc_1_20
        mem_Icc_9_10 mem_Icc_half mem_Icc_half) () (.wrong, false) = 12 / 1433 := by
  simp only [posteriorSilent, pressMass, Fintype.sum_prod_type, Fintype.sum_bool, World.sum_eq,
    legitMix, legitPrior, legitWeight, legitPress, twoPoint_right, twoPoint_wrong, twoPress]
  norm_num

/-- So at `q = 1/2` the level set `{o : P(wrong | o) = 4/81}` is `{Pr}`: the two posteriors differ. -/
theorem lm_half_level_set_is_press : (4 / 81 : ℝ) ≠ 12 / 1433 := by norm_num

/-- The mixture's silence posterior on `wrong` at `q = 1/4`: `32/2433`, not `48/1567`. -/
theorem lm_quarter_silence_posterior :
    posteriorSilent (legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/4) mem_Icc_1_50 mem_Icc_1_20
        mem_Icc_9_10 mem_Icc_half mem_Icc_quarter) () (.wrong, true) +
      posteriorSilent (legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/4) mem_Icc_1_50 mem_Icc_1_20
        mem_Icc_9_10 mem_Icc_half mem_Icc_quarter) () (.wrong, false) = 32 / 2433 := by
  simp only [posteriorSilent, pressMass, Fintype.sum_prod_type, Fintype.sum_bool, World.sum_eq,
    legitMix, legitPrior, legitWeight, legitPress, twoPoint_right, twoPoint_wrong, twoPress]
  norm_num

/-- So at `q = 1/4` the level set `{o : P(wrong | o) = 48/1567}` is `{Pr}`. -/
theorem lm_quarter_level_set_is_press : (48 / 1567 : ℝ) ≠ 32 / 2433 := by norm_num

/-- **General:** the mixture's press posterior equals the prior `ε` iff `α = β` (for `0 < q`,
`0 < ε < 1`, `0 < P(Pr)`): the mixture press is informative about `ω` exactly under the theorem's
hypothesis `α ≠ β`, so the level set at `c = P(wrong | Pr)` is the press event and reading (A)'s
press-branch test is §2.11's equation at that level, not a proxy. -/
theorem lm_press_informative_iff (ε α β c h γ q : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hpm : 0 < q * (ε * β + (1 - ε) * α) + (1 - q) * γ) :
    ((legitMix ε α β c h γ q hε hα hβ hγ hq).posteriorPress () (.wrong, true) +
        (legitMix ε α β c h γ q hε hα hβ hγ hq).posteriorPress () (.wrong, false) = ε) ↔
      α = β := by
  rw [legitMix_posteriorPress_wrong_own, div_eq_iff hpm.ne']
  constructor
  · intro H
    have hkey : q * (1 - ε) * (β - α) * ε = 0 := by linear_combination H
    rcases mul_eq_zero.mp hkey with h0 | h0
    · rcases mul_eq_zero.mp h0 with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact absurd h2 hq0.ne'
        · linarith
      · linarith
    · exact absurd h0 hε0.ne'
  · intro H; subst H; ring

end Cleanroom.Corrigibility.CorrPositionFinds.AuditR3
