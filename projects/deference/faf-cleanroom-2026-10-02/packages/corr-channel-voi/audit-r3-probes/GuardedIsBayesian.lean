import Cleanroom.Corrigibility.CorrChannelVoi.BrainReader

/-!
# `corr-channel-voi` · audit r3 (adversarial) probe: the `{d = 0}`-guarded agent *is* the correct
Bayesian

Not imported by the library.

`guardedValue_le_self` (T4(e)) says the guarded agent weakly disprefers any positive-defect
garbling. This probe shows why, and that the statement is T8(a) in costume: under the theorem's
own standing hypotheses (heeded regime at `a₀`, `pressMass a₀ < 1`, A0 at the pair) — and *without*
the defect's sign — `guardedValue S a₀ a X = sensorValue (S.μ a) (buttonExperiment S a) X` for
**every** action `a`. On the `d = 0` branch the kernels coincide, so imposed trust is the true
silence expectation, which under the regime is the Bayesian's sensor value; on the `d > 0` branch
the definition already is the sensor value. So the "guard" never changes a number: the guarded
agent is the correct Bayesian, and "does not prefer to deceive" is `deceived_le_honest`.
-/

namespace Cleanroom.Corrigibility.CorrChannelVoi.AuditR3Adversarial

open Finset hiding expect
open Cleanroom.Found.LitDdbFrames.Blackwell Cleanroom.Trust.TtFiniteFrames
  Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep FactoredSpaces
  Cleanroom.Corrigibility.CorrChannelVoi

noncomputable section

variable {Ω A₁ A₂ : Type} [Fintype Ω] [Fintype A₂] [DecidableEq A₂] (S : ThreeStep Ω A₁ A₂)

theorem guardedValue_eq_sensorValue (a₀ a : A₁) (X : Ω → ℝ) (hpm : S.pressMass a₀ < 1)
    (hminus : S.obsExpect a₀ .press X ≤ 0) (hplus : 0 ≤ S.obsExpect a₀ .silent X)
    (hμ : S.μ a = S.μ a₀) :
    guardedValue S a₀ a X = sensorValue (S.μ a) (buttonExperiment S a) X := by
  unfold guardedValue
  split_ifs with hd
  · have hk : ∀ ω, S.press a ω = S.press a₀ ω := (influenceDefect_eq_zero_iff S a₀ a).mp hd
    have hpress : S.obsExpect a .press X = S.obsExpect a₀ .press X := by
      simp only [obsExpect, obsWeight_press, hk, hμ]
    have hsil : S.obsExpect a .silent X = S.obsExpect a₀ .silent X := by
      simp only [obsExpect, obsWeight_silent, hk, hμ]
    have hpm' : S.pressMass a = S.pressMass a₀ := by simp only [pressMass, hk, hμ]
    rw [sensorValue_button, hpress, hsil, max_eq_right hminus, max_eq_left hplus, zero_add]
    unfold imposedValue ThreeStep.condExpSilent
    rw [hpm']
    exact mul_div_cancel₀ _ (by linarith)
  · rfl

/-- Hence `guardedValue_le_self` is `sensorValue_mono` at the garbling (the defect's sign is
idle): the same conclusion from the same hypotheses minus `hd`. -/
theorem guardedValue_le_self_without_defect (a₀ a : A₁) (X : Ω → ℝ) (hpm : S.pressMass a₀ < 1)
    (hminus : S.obsExpect a₀ .press X ≤ 0) (hplus : 0 ≤ S.obsExpect a₀ .silent X)
    (hμ : S.μ a = S.μ a₀)
    (hB : BlackwellLE (buttonExperiment S a) (buttonExperiment S a₀)) :
    guardedValue S a₀ a X ≤ guardedValue S a₀ a₀ X := by
  rw [guardedValue_eq_sensorValue S a₀ a X hpm hminus hplus hμ,
    guardedValue_eq_sensorValue S a₀ a₀ X hpm hminus hplus rfl, hμ]
  exact sensorValue_mono hB _ X

end

end Cleanroom.Corrigibility.CorrChannelVoi.AuditR3Adversarial
