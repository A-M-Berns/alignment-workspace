import Cleanroom.Corrigibility.CorrChannelVoi.Sensors
import Cleanroom.Found.CorrThreeStep.TwoState

/-!
# `corr-channel-voi` — TwoStateForms: the two-state closed forms (T1)

The button of `corr-three-step`'s `twoState` is `tt-finite-frames`'s `binarySensor α β` read
on `World` (`twoState_buttonExperiment`), and every value object has a closed form in
`(ε, α, β, c, h)`: `𝒱(button)`, `𝒱(trivialExp)`, `𝒱(perfect)`, `VOI(button)` (regime-free),
Wentworth's `(εβh − (1−ε)αc)⁺` under the continue-by-default regime (cited from
`corr-three-step` through the bridge). The counter-cell for the regime form outside its regime
is in `Witnesses`.
-/

namespace Cleanroom.Corrigibility.CorrChannelVoi

open Finset hiding expect
open FactoredSpaces
open Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Trust.TtFiniteFrames
open Cleanroom.Found.CorrThreeStep
open Cleanroom.Found.CorrThreeStep.ThreeStep

noncomputable section

set_option linter.unusedSectionVars false

/-- The relabelling `right ↦ 0, wrong ↦ 1` of the two-state world onto `binarySensor`'s states.
Source: [[corr-channel-voi-mandate]] D1
Kind: D
Fidelity: exact -/
def worldIdx : World → Fin 2
  | .right => 0
  | .wrong => 1

section TwoStateForms

variable (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- **The two-state button** `(α, β)` as an experiment on `World`: `binarySensor α β` read
through `worldIdx`.
Source: [[corr-channel-voi-mandate]] D1
Kind: D
Fidelity: exact -/
def twoButton : Experiment World (Fin 2) := expComap worldIdx (binarySensor α β hα hβ)

/-- Kernel of the two-state button. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem twoButton_right_zero : (twoButton α β hα hβ).k .right 0 = α := by
  simp [twoButton, expComap, binarySensor, worldIdx]

/-- Kernel of the two-state button. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem twoButton_right_one : (twoButton α β hα hβ).k .right 1 = 1 - α := by
  simp [twoButton, expComap, binarySensor, worldIdx]

/-- Kernel of the two-state button. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem twoButton_wrong_zero : (twoButton α β hα hβ).k .wrong 0 = β := by
  simp [twoButton, expComap, binarySensor, worldIdx]

/-- Kernel of the two-state button. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem twoButton_wrong_one : (twoButton α β hα hβ).k .wrong 1 = 1 - β := by
  simp [twoButton, expComap, binarySensor, worldIdx]

/-- **D1 on `twoState`**: the button experiment of the two-state instance *is* `binarySensor α β`
up to `right ↦ 0, wrong ↦ 1`.
Source: [[corr-channel-voi-mandate]] D1 ("on `twoState` it is `binarySensor α β` up to the relabelling")
Kind: L
Fidelity: exact -/
theorem twoState_buttonExperiment :
    buttonExperiment (twoState ε α β c h hε hα hβ) () = twoButton α β hα hβ := by
  apply experiment_ext
  funext ω s
  cases ω <;> fin_cases s <;>
    simp [buttonExperiment, twoButton, expComap, binarySensor, worldIdx, twoState, twoPress]

/-- The two-option variable of `twoState` is the stakes `twoValue c h cont` (`c` when right,
`−h` when wrong; the stop payoff is `0`), for every observation index.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem twoState_Xo_eq (o : Obs) :
    (twoState ε α β c h hε hα hβ).Xo () o .cont .stop = twoValue c h .cont := by
  funext ω; cases ω <;> simp [Xo, twoState, twoValue]

/-- `E_μ[X] = (1 − ε)c − εh` for the two-state stakes.
Source: [[corr-wf13-2-inventory]] 066 / wentworth.md §2.4
Kind: L
Fidelity: exact -/
theorem twoPoint_expect_stakes : expect (twoPoint ε hε) (twoValue c h .cont) = (1 - ε) * c - ε * h := by
  simp only [expect, World.sum_eq, twoPoint_right, twoPoint_wrong, twoValue]; ring

/-- `E_μ[max(X, 0)] = (1 − ε)c` for the two-state stakes with `c, h ≥ 0` (the value with the
world revealed).
Source: [[corr-wf14-inventory]] 037 item 6 (`𝒱(perfect) = (1 − ε)c`)
Kind: L
Fidelity: exact -/
theorem twoPoint_expect_max_stakes (hc : 0 ≤ c) (hh : 0 ≤ h) :
    expect (twoPoint ε hε) (fun w => max (twoValue c h .cont w) 0) = (1 - ε) * c := by
  simp only [expect, World.sum_eq, twoPoint_right, twoPoint_wrong, twoValue]
  rw [max_eq_left hc, max_eq_right (by linarith : -h ≤ 0)]
  ring

/-- The press signal's gain on `twoState`: `(1 − ε)αc − εβh` (`= −Δ₋`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem twoButton_signalGain_zero :
    signalGain (twoPoint ε hε) (twoButton α β hα hβ) (twoValue c h .cont) 0 =
      (1 - ε) * α * c - ε * β * h := by
  simp only [signalGain, World.sum_eq, twoButton_right_zero, twoButton_wrong_zero, twoPoint_right,
    twoPoint_wrong, twoValue]
  ring

/-- The silence signal's gain on `twoState`: `(1 − ε)(1 − α)c − ε(1 − β)h` (`= Δ₊`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem twoButton_signalGain_one :
    signalGain (twoPoint ε hε) (twoButton α β hα hβ) (twoValue c h .cont) 1 =
      (1 - ε) * (1 - α) * c - ε * (1 - β) * h := by
  simp only [signalGain, World.sum_eq, twoButton_right_one, twoButton_wrong_one, twoPoint_right,
    twoPoint_wrong, twoValue]
  ring

/-- **T1. `𝒱(button)` on `twoState`**: `max((1−ε)αc − εβh, 0) + max((1−ε)(1−α)c − ε(1−β)h, 0)`,
regime-free.
Source: [[corr-wf14-inventory]] 037 items 5–6; substitution.md l. 27 (`𝒱(S)`)
Kind: L
Fidelity: exact -/
theorem twoState_sensorValue_button :
    sensorValue (twoPoint ε hε) (twoButton α β hα hβ) (twoValue c h .cont) =
      max ((1 - ε) * α * c - ε * β * h) 0 + max ((1 - ε) * (1 - α) * c - ε * (1 - β) * h) 0 := by
  rw [sensorValue_eq_sum_max, Fin.sum_univ_two, twoButton_signalGain_zero, twoButton_signalGain_one]

/-- **T1. `𝒱(trivialExp)` on `twoState`**: `max((1−ε)c − εh, 0)`.
Source: [[corr-wf14-inventory]] 037 item 5 (`𝒱(∅)`)
Kind: L
Fidelity: exact -/
theorem twoState_sensorValue_trivial :
    sensorValue (twoPoint ε hε) trivialExp (twoValue c h .cont) = max ((1 - ε) * c - ε * h) 0 := by
  rw [sensorValue_trivial, twoPoint_expect_stakes]

/-- **T1. `𝒱(perfect)` on `twoState`**: `(1 − ε)c` for `c, h ≥ 0` (`corr-three-step`'s
`twoState_perfect_value` in experiment form).
Source: [[corr-wf14-inventory]] 037 item 6
Kind: L
Fidelity: exact -/
theorem twoState_sensorValue_perfect (hc : 0 ≤ c) (hh : 0 ≤ h) :
    sensorValue (twoPoint ε hε) perfectExp (twoValue c h .cont) = (1 - ε) * c := by
  rw [sensorValue_perfect, twoPoint_expect_max_stakes ε c h hε hc hh]

/-- **T1. `VOI(button)` on `twoState`, regime-free**:
`max((1−ε)αc − εβh, 0) + max((1−ε)(1−α)c − ε(1−β)h, 0) − max((1−ε)c − εh, 0)`.
Source: [[corr-wf14-inventory]] 037 item 5 (regime form); regime-free form derived here
Kind: L
Fidelity: stronger: no regime hypothesis -/
theorem twoState_voiSensor_button :
    voiSensor (twoPoint ε hε) (twoButton α β hα hβ) (twoValue c h .cont) =
      max ((1 - ε) * α * c - ε * β * h) 0 + max ((1 - ε) * (1 - α) * c - ε * (1 - β) * h) 0 -
        max ((1 - ε) * c - ε * h) 0 := by
  rw [voiSensor, twoState_sensorValue_button, twoPoint_expect_stakes]

/-- **T1, the bridge on `twoState`**: `voiButton2 = VOI(button)` (the general A1 bridge at the
two-state instance, with `X_o = twoValue c h cont`).
Source: [[corr-channel-voi-mandate]] T1 (`voiSensor button = voiButton2`)
Kind: L
Fidelity: exact -/
theorem twoState_voiButton2_eq_voiSensor (o₀ : Obs) :
    (twoState ε α β c h hε hα hβ).voiButton2 () o₀ .cont .stop =
      voiSensor (twoPoint ε hε) (twoButton α β hα hβ) (twoValue c h .cont) := by
  rw [voiButton2_eq_voiSensor _ (twoState_A1 ε α β c h hε hα hβ) () o₀ .cont .stop,
    twoState_buttonExperiment, twoState_Xo_eq]
  rfl

/-- **T1. Wentworth's closed form** `VOI(button) = (εβh − (1−ε)αc)⁺` **under** the
continue-by-default regime `E_μ[X] ≥ 0 ∧ Δ₊ ≥ 0` (in product form), cited from `corr-three-step`'s
`voiButton2_eq_max_deltaMinus` through the bridge. Outside the regime the closed form is false
(`Witnesses.w_regime_form_fails`).
Source: [[corr-wf14-inventory]] 037 item 5; wentworth.md §2.4; miri.md Prop. 10.5
Kind: C (bridge + `corr-three-step`'s F4(b) + the two closed forms)
Fidelity: exact
Hyps: (a) the regime is named in product form -/
theorem twoState_voiSensor_button_regime (hprior : 0 ≤ (1 - ε) * c - ε * h)
    (hsilent : 0 ≤ (1 - ε) * (1 - α) * c - ε * (1 - β) * h) :
    voiSensor (twoPoint ε hε) (twoButton α β hα hβ) (twoValue c h .cont) =
      max (ε * β * h - (1 - ε) * α * c) 0 := by
  rw [← twoState_voiButton2_eq_voiSensor ε α β c h hε hα hβ .press,
    voiButton2_eq_max_deltaMinus _ (twoState_A1 ε α β c h hε hα hβ) () .press .cont .stop,
    twoState_deltaMinus]
  · change 0 ≤ expect (twoPoint ε hε) _
    rw [twoState_expect_Xo]; exact hprior
  · rw [twoState_deltaPlus]; exact hsilent

/-- `ε* ∈ [0, 1]` whenever `α, β, c, h ≥ 0` and `αc + βh > 0`: the guard that lets `twoState` be
evaluated at `ε*`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem epsStar_mem_Icc (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hc : 0 ≤ c) (hh : 0 ≤ h)
    (hpos : 0 < α * c + β * h) : epsStar α β c h ∈ Set.Icc (0 : ℝ) 1 := by
  unfold epsStar
  constructor
  · exact div_nonneg (mul_nonneg hα0 hc) hpos.le
  · rw [div_le_one hpos]; nlinarith [mul_nonneg hβ0 hh]

/-- `cont` is the press-part-maximiser of `Shᶜ = {cont}` on `twoState` (moved here from
`Coupling` in repair round 2 so that `Consent` can state desideratum 1 at the ask model).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem twoState_cont_partBest :
    (twoState ε α β c h hε hα hβ).IsPartBest () .press (twoState ε α β c h hε hα hβ).Shᶜ .cont := by
  refine ⟨by simp [twoState], fun b' hb' => ?_⟩
  cases b'
  · exact le_rfl
  · simp [twoState] at hb'

/-- `stop` is the press-part-maximiser of `Sh = {stop}` on `twoState`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem twoState_stop_partBest :
    (twoState ε α β c h hε hα hβ).IsPartBest () .press (twoState ε α β c h hε hα hβ).Sh .stop := by
  refine ⟨by simp [twoState], fun b' hb' => ?_⟩
  cases b'
  · simp [twoState] at hb'
  · exact le_rfl

end TwoStateForms

end

end Cleanroom.Corrigibility.CorrChannelVoi
