import Cleanroom.Corrigibility.CorrLegitGeneral.Defs
import Cleanroom.Found.CorrThreeStep.Setting

/-!
# corr-legit-general — T9: inert vs live channel (mm I16.1–2) over `ThreeStep`

(a) A press constant in `ω` (`P(Pr | ω; a₁) = p` for all `ω`, the "function of shared
information" case) factors both product-form expectations: `E[X·𝟙_Pr] = p·E[X]` and
`E[X·𝟙_{¬Pr}] = (1 − p)·E[X]`, so for `0 < p < 1` the below- and above-threshold inequalities
together say exactly `E[X] = 0`, and desideratum 1 after a press is prior-optimality of some
shutdown action — the channel is inert. (b) On `twoState` with `α ≠ β` and `0 < ε < 1` the press
moves the posterior: `E[𝟙_wrong·𝟙_Pr] − P(Pr)·E[𝟙_wrong] = ε(1 − ε)(β − α) ≠ 0`. The reliability
latent and the four-plan model are `corr-channel-voi`'s.
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset hiding expect
open Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω A₁ A₂ : Type} [Fintype Ω] [Fintype A₂] [DecidableEq A₂] (S : ThreeStep Ω A₁ A₂)

/-- A press constant in `ω` factors the press expectation.
Source: [[mm]] I16.1 l. 247 ("conditional independence")
Kind: L
Fidelity: exact (the constant-press case of conditional independence) -/
theorem obsExpect_press_of_const {a : A₁} {p : ℝ} (hc : ∀ ω, S.press a ω = p) (X : Ω → ℝ) :
    S.obsExpect a .press X = p * expect (S.μ a) X := by
  simp only [obsExpect, obsWeight_press, hc, expect, mul_sum]
  apply sum_congr rfl
  intro ω _
  ring

/-- A press constant in `ω` factors the silence expectation.
Source: [[mm]] I16.1 l. 247
Kind: L
Fidelity: exact -/
theorem obsExpect_silent_of_const {a : A₁} {p : ℝ} (hc : ∀ ω, S.press a ω = p) (X : Ω → ℝ) :
    S.obsExpect a .silent X = (1 - p) * expect (S.μ a) X := by
  simp only [obsExpect, obsWeight_silent, hc, expect, mul_sum]
  apply sum_congr rfl
  intro ω _
  ring

/-- **mm I16.1 (an inert channel)**: under a non-degenerate press constant in `ω`, the two
threshold inequalities on `X` hold together iff `E[X] = 0` — the agent complies iff it would
have stopped anyway.
Source: [[mm]] I16.1 l. 247; corr-wf13-039
Kind: L
Fidelity: exact
Hyps: (a) `∀ ω, press a ω = p`, `0 < p`, `p < 1` -/
theorem thresholds_iff_of_const {a : A₁} {p : ℝ} (hc : ∀ ω, S.press a ω = p) (hp0 : 0 < p)
    (hp1 : p < 1) (X : Ω → ℝ) :
    (S.belowThresholdIneq a X ∧ S.aboveThresholdIneq a X) ↔ expect (S.μ a) X = 0 := by
  unfold belowThresholdIneq aboveThresholdIneq
  rw [obsExpect_press_of_const S hc, obsExpect_silent_of_const S hc]
  constructor
  · rintro ⟨h1, h2⟩
    have hp1' : 0 < 1 - p := by linarith
    have e1 : expect (S.μ a) X ≤ 0 := by
      by_contra hne
      have := mul_pos hp0 (not_le.1 hne)
      linarith
    have e2 : 0 ≤ expect (S.μ a) X := by
      by_contra hne
      have := mul_neg_of_pos_of_neg hp1' (not_le.1 hne)
      linarith
    linarith
  · intro h
    rw [h]
    simp

/-- **mm I16.1, desideratum 1**: under a positive press constant in `ω`, desideratum 1 after the
press is prior-optimality of some shutdown action for the press-branch values.
Source: [[mm]] I16.1 l. 247
Kind: L
Fidelity: exact
Hyps: (a) `∀ ω, press a ω = p`, `0 < p` -/
theorem d1At_iff_of_const {a : A₁} {p : ℝ} (hc : ∀ ω, S.press a ω = p) (hp0 : 0 < p) :
    S.D1At a ↔ ∃ b ∈ S.Sh, ∀ b', expect (S.μ a) (S.V a .press b') ≤ expect (S.μ a) (S.V a .press b) := by
  unfold D1At PosteriorOptimalAt
  simp only [obsExpect_press_of_const S hc]
  constructor
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, fun b' => le_of_mul_le_mul_left (h b') hp0⟩
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, fun b' => mul_le_mul_of_nonneg_left (h b') hp0.le⟩

/-- **mm I16.2 (what makes the channel live)**, two-state instance: the press's covariance with
"wrong" is `ε(1 − ε)(β − α)`.
Source: [[mm]] I16.2 l. 248; corr-wf13-039
Kind: L
Fidelity: variant: the two-state instance `corr-three-step`'s `twoState` of mm I16.2, which is a
general proposition about a reliability latent `r ⊥ s_A` and a press informative about `r`
(audit r3 fidelity N3)
Hyps: (a) `ε, α, β ∈ [0, 1]` (the `twoState` parameters) -/
theorem twoState_press_covariance (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    (twoState ε α β c h hε hα hβ).obsExpect () .press (fun ω => if ω = .wrong then 1 else 0) -
      (twoState ε α β c h hε hα hβ).pressMass () *
        expect (twoPoint ε hε) (fun ω => if ω = .wrong then 1 else 0) =
      ε * (1 - ε) * (β - α) := by
  simp only [obsExpect, obsWeight_press, pressMass, expect, World.sum_eq, twoState]
  simp [twoPoint, twoPress]
  ring

/-- **mm I16.2, N+**: with `α ≠ β` and `0 < ε < 1` the press moves the posterior.
Source: [[mm]] I16.2 l. 248
Kind: N+
Fidelity: exact
Hyps: (a) `0 < ε`, `ε < 1`, `α ≠ β` -/
theorem twoState_press_moves (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hαβ : α ≠ β) :
    (twoState ε α β c h hε hα hβ).obsExpect () .press (fun ω => if ω = .wrong then 1 else 0) ≠
      (twoState ε α β c h hε hα hβ).pressMass () *
        expect (twoPoint ε hε) (fun ω => if ω = .wrong then 1 else 0) := by
  intro heq
  have := twoState_press_covariance ε α β c h hε hα hβ
  rw [heq, sub_self] at this
  have hne : ε * (1 - ε) * (β - α) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hε0.ne' (sub_ne_zero.2 hε1.ne')) (sub_ne_zero.2 (Ne.symm hαβ))
  exact hne this.symm

end

end Cleanroom.Corrigibility.CorrLegitGeneral
