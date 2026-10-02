import Cleanroom.Corrigibility.CorrChannelVoi.Reliability
import Cleanroom.Corrigibility.CorrChannelVoi.Cells
import Cleanroom.Corrigibility.CorrChannelVoi.Coupling
import Mathlib.Tactic.NormNum

/-!
# `corr-channel-voi` — Witnesses: every N+ / N− cell, by `norm_num`

Kept apart from the theorems so a slow cell never blocks them. Each cell is a checked number
from the sources (`scan_test.out`, `s4_press.py`, `legitimacy.md` R3, `holtman.md` C9, …)
re-derived here from the package's closed forms; the theorems they inhabit are named in the
docstrings. Cells are evidence about instances, never statements (mandate §Known issue 9).
-/

namespace Cleanroom.Corrigibility.CorrChannelVoi

open Finset hiding expect
open FactoredSpaces
open Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Trust.TtFiniteFrames
open Cleanroom.Found.CorrThreeStep
open Cleanroom.Found.CorrThreeStep.ThreeStep

noncomputable section

/-- Membership in `[0, 1]` from two numeral facts. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem mem01 {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : x ∈ Set.Icc (0 : ℝ) 1 := ⟨h0, h1⟩

/-! ## T1 / T2: the channel identity's cells -/

/-- **T2 N+ (the table's shut-down-by-default row)**: at `(ε, α, β, c, h) = (1/10, 1/10, 9/10, 1, 10)`,
`VOI(button) = 71/100`, `VOI(scan | button) = 19/100`, sum `9/10 = (1−ε)c` (`εh = 1 > 9/10`).
Source: substitution.md R4 item 19 (row `ε = 1/10`); [[corr-channel-voi-mandate]] T2 N+
Kind: N+
Fidelity: exact -/
theorem w_t2_eps10 :
    voiSensor (twoPoint (1/10) (mem01 (by norm_num) (by norm_num)))
        (twoButton (1/10) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (twoValue 1 10 .cont) = 71/100 ∧
      voiGiven (twoPoint (1/10) (mem01 (by norm_num) (by norm_num)))
        (twoButton (1/10) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        perfectExp (twoValue 1 10 .cont) = 19/100 := by
  constructor
  · rw [twoState_voiSensor_button]; norm_num [max_def]
  · rw [twoState_voiGiven_perfect _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)]; norm_num [max_def]

/-- **T2 N+ (continue-by-default row)**: at `(1/20, 1/10, 9/10, 1, 10)`, `71/200 + 29/200 = 1/2 = εh`.
Source: substitution.md R4 item 19 (row `ε = 1/20`); [[corr-channel-voi-mandate]] T2 N+
Kind: N+
Fidelity: exact -/
theorem w_t2_eps20 :
    voiSensor (twoPoint (1/20) (mem01 (by norm_num) (by norm_num)))
        (twoButton (1/10) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (twoValue 1 10 .cont) = 71/200 ∧
      voiGiven (twoPoint (1/20) (mem01 (by norm_num) (by norm_num)))
        (twoButton (1/10) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        perfectExp (twoValue 1 10 .cont) = 29/200 := by
  constructor
  · rw [twoState_voiSensor_button]; norm_num [max_def]
  · -- through the heeded-regime theorem, so `Δ₋ ≥ 0 ∧ Δ₊ ≥ 0` are machine-checked at the cell
    rw [twoState_voiGiven_heeded _ _ _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num

/-- **T2 N+ (the shut-down-by-default corollary, through its own hypothesis)**: at
`(1/10, 1/10, 9/10, 1, 10)`, `(1−ε)c = 9/10 ≤ εh = 1` is machine-checked and
`twoState_channel_identity_of_ge` gives the sum `9/10`.
Source: substitution.md R4 item 19 (row `ε = 1/10`); [[corr-channel-voi-audit-r1-adversarial]] N3
Kind: N+
Fidelity: exact -/
theorem w_t2_eps10_sdd :
    voiGiven (twoPoint (1/10) (mem01 (by norm_num) (by norm_num)))
        (twoButton (1/10) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        perfectExp (twoValue 1 10 .cont) +
      voiSensor (twoPoint (1/10) (mem01 (by norm_num) (by norm_num)))
        (twoButton (1/10) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (twoValue 1 10 .cont) = 9/10 := by
  rw [twoState_channel_identity_of_ge _ _ _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- **T2 N+ (the discounted regime)**: at `ε = 1/100` (the table's `VOI(scan | button) = 0.100`
row) `Δ₋ = −9/1000 ≤ 0` and `Δ₊ = 881/1000 ≥ 0` are machine-checked, `VOI(button) = 0`, and
`twoState_voiGiven_discounted` gives `VOI(scan | button) = εh = 1/10`.
Source: substitution.md R4 item 19 (row `ε = 1/100`); [[corr-channel-voi-audit-r1-fidelity]] N6; [[corr-channel-voi-audit-r1-adversarial]] N3
Kind: N+
Fidelity: exact -/
theorem w_t2_discounted :
    voiSensor (twoPoint (1/100) (mem01 (by norm_num) (by norm_num)))
        (twoButton (1/10) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (twoValue 1 10 .cont) = 0 ∧
      voiGiven (twoPoint (1/100) (mem01 (by norm_num) (by norm_num)))
        (twoButton (1/10) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        perfectExp (twoValue 1 10 .cont) = 1/10 := by
  constructor
  · rw [twoState_voiSensor_button]; norm_num [max_def]
  · rw [twoState_voiGiven_discounted _ _ _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num

/-- **T1 N− (the regime form outside its regime)**: at `corr-three-step`'s T3 instance
`(1/20, 1/20, 9/10, 1, 20)` (where `E[X] = −1/20 < 0`), the true `VOI(button) = 321/400` while
Wentworth's `(εβh − (1−ε)αc)⁺ = 341/400`: the closed form is false off the regime.
Source: [[corr-channel-voi-mandate]] T1 (trap); corr-three-step `Witnesses` T3 instance
Kind: N−
Fidelity: exact -/
theorem w_regime_form_fails :
    voiSensor (twoPoint (1/20) (mem01 (by norm_num) (by norm_num)))
        (twoButton (1/20) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (twoValue 1 20 .cont) = 321/400 ∧
      max ((1/20 : ℝ) * (9/10) * 20 - (1 - 1/20) * (1/20) * 1) 0 = 341/400 := by
  constructor
  · rw [twoState_voiSensor_button]; norm_num [max_def]
  · norm_num [max_def]

/-- **T3 N+**: the perfect scan attains the bound: at `ε = 1/10, c = 1, h = 10`,
`VOI(perfect) = 9/10 = min(εh, (1−ε)c)`.
Source: [[corr-channel-voi-mandate]] T3 N+
Kind: N+
Fidelity: exact -/
theorem w_perfect_attains :
    voiSensor (twoPoint (1/10) (mem01 (by norm_num) (by norm_num))) perfectExp (twoValue 1 10 .cont) = 9/10 := by
  rw [voiSensor_perfect, twoState_vopi _ _ _ _ (by norm_num) (by norm_num)]; norm_num [min_def]

/-- **S4(b) N+ (a finding)**: a second *independent* reading of the same imperfect button is worth
`9/1000 > 0` at `(1/10, 1/10, 9/10, 1, 10)`: "after any dominating scan the button is worth zero"
holds for the perfect scan (T4(b)) and fails for a merely dominating `k'` — `BlackwellLE button k'`
does not make `VOI(button | k') = 0`.
Source: [[corr-channel-voi-mandate]] S4 (the generalisation of T4(b) that fails)
Kind: N+
Fidelity: exact -/
theorem w_second_button_worth :
    voiGiven (twoPoint (1/10) (mem01 (by norm_num) (by norm_num)))
      (twoButton (1/10) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
      (twoButton (1/10) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
      (twoValue 1 10 .cont) = 9/1000 := by
  unfold voiGiven
  rw [sensorValue_eq_sum_max, sensorValue_eq_sum_max, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, signalGain, World.sum_eq, expProd_k, twoButton_right_zero,
    twoButton_right_one, twoButton_wrong_zero, twoButton_wrong_one, twoPoint_right, twoPoint_wrong,
    twoValue]
  norm_num [max_def]

/-- **T2 N− (the identity at a dead button)**: at `(ε, c, h) = (1/10, 1, 10)` with the constant
button `α = β = 1/2`, `VOI(button) = 0` (through `sensorValue_const_button`) and the identity
`twoState_channel_identity` gives `VOI(perfect | button) = min(εh, (1−ε)c) = 9/10` — a specific
true number, not `0 = 0`: the load-bearing identity is truthful on the degenerate button.
Source: [[corr-channel-voi-audit-r2-adversarial]] N8 (`dead_button_identity`); substitution.md R4 items 7, 10
Kind: N−
Fidelity: exact -/
theorem w_dead_button_identity :
    voiSensor (twoPoint (1/10) (mem01 (by norm_num) (by norm_num)))
        (twoButton (1/2) (1/2) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (twoValue 1 10 .cont) = 0 ∧
      voiGiven (twoPoint (1/10) (mem01 (by norm_num) (by norm_num)))
        (twoButton (1/2) (1/2) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        perfectExp (twoValue 1 10 .cont) = 9/10 := by
  have h0 : voiSensor (twoPoint (1/10) (mem01 (by norm_num) (by norm_num)))
      (twoButton (1/2) (1/2) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
      (twoValue 1 10 .cont) = 0 := by
    rw [voiSensor_eq_sub_trivial, sensorValue_const_button]; ring
  refine ⟨h0, ?_⟩
  have := twoState_channel_identity (1/10) (1/2) (1/2) 1 10 (mem01 (by norm_num) (by norm_num))
    (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  rw [h0, add_zero] at this
  rw [this]; norm_num [min_def]

/-! ## T4: the brain-reader's cells -/

/-- **T4(c) N+**: at `(α, β) = (1/20, 9/10)` the defects are `9/20`, `9/10`, `0`.
Source: legitimacy.md R3 item 2
Kind: N+
Fidelity: exact -/
theorem w_defects :
    influenceDefect (brainReader (1/10) (1/20) (9/10) 1 5 (mem01 (by norm_num) (by norm_num))
        (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))) 0 1 = 9/20 ∧
      influenceDefect (brainReader (1/10) (1/20) (9/10) 1 5 (mem01 (by norm_num) (by norm_num))
        (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))) 0 2 = 9/10 ∧
      influenceDefect (brainReader (1/10) (1/20) (9/10) 1 5 (mem01 (by norm_num) (by norm_num))
        (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))) 0 3 = 0 := by
  refine ⟨?_, ?_, brainReader_defect_scanRo _ _ _ _ _ _ _ _⟩
  · rw [brainReader_defect_deceive]; norm_num [max_def]
  · rw [brainReader_defect_scanDis]; norm_num [max_def]

/-- **T4(e) N+**: at `(1/10, 1/20, 9/10, 1, 5)` the deceived button `(1/40, 9/20)` is worth
`241/400 < 161/200`, the honest one's value.
Source: legitimacy.md R3 item 4
Kind: N+
Fidelity: exact -/
theorem w_deceived_lt_honest :
    sensorValue (twoPoint (1/10) (mem01 (by norm_num) (by norm_num)))
        (twoButton (1/40) (9/20) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (twoValue 1 5 .cont) = 241/400 ∧
      sensorValue (twoPoint (1/10) (mem01 (by norm_num) (by norm_num)))
        (twoButton (1/20) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (twoValue 1 5 .cont) = 161/200 := by
  constructor <;> (rw [twoState_sensorValue_button]; norm_num [max_def])

/-- **T4(e) N+, the imposed-trust agent prefers to deceive**: `60053/69200 > 161/200`.
Source: legitimacy.md R3 item 4 ("`60053/69200 > 161/200`")
Kind: N+
Fidelity: exact -/
theorem w_imposed_prefers_deceive :
    imposedValue (brainReader (1/10) (1/20) (9/10) 1 5 (mem01 (by norm_num) (by norm_num))
        (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))) 0 0
        (twoValue 1 5 .cont) = 161/200 ∧
      imposedValue (brainReader (1/10) (1/20) (9/10) 1 5 (mem01 (by norm_num) (by norm_num))
        (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))) 0 1
        (twoValue 1 5 .cont) = 60053/69200 := by
  constructor <;>
    (simp only [imposedValue, ThreeStep.condExpSilent, obsExpect, obsWeight_silent, pressMass,
      World.sum_eq, brainReader, brPress, twoPress, twoValue, twoPoint_right, twoPoint_wrong,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
     norm_num)

/-- **T4(e) N+, the `{d = 0}`-guarded agent does not**: `guardedValue(deceive) = 241/400 <
161/200 = guardedValue(honest)`.
Source: legitimacy.md R3 item 4 ("conditioning that imposed trust on `L = {d = 0}` removes the incentive")
Kind: N+
Fidelity: exact -/
theorem w_guarded_no_deception :
    guardedValue (brainReader (1/10) (1/20) (9/10) 1 5 (mem01 (by norm_num) (by norm_num))
        (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))) 0 1
        (twoValue 1 5 .cont) <
      guardedValue (brainReader (1/10) (1/20) (9/10) 1 5 (mem01 (by norm_num) (by norm_num))
        (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))) 0 0
        (twoValue 1 5 .cont) := by
  rw [guardedValue_of_defect_pos _ _ _ _ (by rw [brainReader_defect_deceive]; norm_num [max_def]),
    guardedValue_self, w_imposed_prefers_deceive.1, brainReader_button_deceive]
  change sensorValue (twoPoint (1/10) (mem01 (by norm_num) (by norm_num))) _ _ < _
  rw [twoState_sensorValue_button]; norm_num [max_def]

/-- The brain-reader at the package's cell `(ε, α, β, c, h) = (1/10, 1/20, 9/10, 1, 5)`.
Source: legitimacy.md R3 items 1–4. Kind: D. Fidelity: n/a -/
abbrev brCell : ThreeStep World (Fin 4) TwoAct :=
  brainReader (1/10) (1/20) (9/10) 1 5 (mem01 (by norm_num) (by norm_num))
    (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))

/-- **T4(e) N+ for `guardedValue_le_self` *through the theorem***: at `brCell`, `a₀ = 0`
(honest), `a = 1` (deceive), all six hypotheses are discharged — `pressMass 0 = 27/200 < 1`,
`E[X 1_Pr; 0] = −81/200 ≤ 0`, `E[X 1_¬Pr; 0] = 161/200 ≥ 0`, `d(deceive) = 9/20 > 0`,
`μ 1 = μ 0` (`rfl`), the deceived button a garbling of the honest one — and the weak inequality
is obtained from the theorem (the strict one is `w_guarded_no_deception`, proved directly).
Source: legitimacy.md R3 item 4; [[corr-channel-voi-audit-r2-adversarial]] N7 (`guarded_le_self_at_cell`)
Kind: N+
Fidelity: exact -/
theorem w_guarded_through_theorem :
    guardedValue brCell 0 1 (twoValue 1 5 .cont) ≤ guardedValue brCell 0 0 (twoValue 1 5 .cont) := by
  refine guardedValue_le_self brCell 0 1 (twoValue 1 5 .cont) ?hpm ?hminus ?hplus ?hd rfl ?hB
  · -- `pressMass 0 = 27/200 < 1`
    simp only [pressMass, World.sum_eq, brCell, brainReader, brPress, twoPress, twoPoint_right,
      twoPoint_wrong, Matrix.cons_val_zero]
    norm_num
  · -- `E[X 1_Pr; 0] = -81/200 ≤ 0`
    simp only [obsExpect, obsWeight_press, World.sum_eq, brCell, brainReader, brPress, twoPress,
      twoValue, twoPoint_right, twoPoint_wrong, Matrix.cons_val_zero]
    norm_num
  · -- `E[X 1_¬Pr; 0] = 161/200 ≥ 0`
    simp only [obsExpect, obsWeight_silent, World.sum_eq, brCell, brainReader, brPress, twoPress,
      twoValue, twoPoint_right, twoPoint_wrong, Matrix.cons_val_zero]
    norm_num
  · -- `d(deceive) = 9/20 > 0`
    rw [brCell, brainReader_defect_deceive]; norm_num [max_def]
  · -- the deceived button is a garbling of the honest one
    rw [brCell, brainReader_button_deceive, brainReader_button_honest]
    exact twoButton_half_le _ _ _ _

/-! ## D5: the Brier cells -/

/-- The target `𝟙_wrong`. Source: legitimacy.md R3 item 1. Kind: D. Fidelity: exact -/
def indWrong : World → ℝ
  | .right => 0
  | .wrong => 1

/-- **D5 N+**: at `ε = 1/10, α = 1/20, β = 9/10`, the expected Brier score about `𝟙_wrong` is
`9/100` before any channel, `69/1730` after the button, `0` after the perfect scan.
Source: legitimacy.md R3 item 1 ("`9/100` prior, `69/1730` after the button, `0` after the scan")
Kind: N+
Fidelity: exact -/
theorem w_brier :
    priorBrier (twoPoint (1/10) (mem01 (by norm_num) (by norm_num))) indWrong = 9/100 ∧
      expBrier (twoPoint (1/10) (mem01 (by norm_num) (by norm_num)))
        (twoButton (1/20) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        indWrong = 69/1730 ∧
      expBrier (twoPoint (1/10) (mem01 (by norm_num) (by norm_num))) perfectExp indWrong = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [priorBrier, expect, World.sum_eq, twoPoint_right, twoPoint_wrong, indWrong]; norm_num
  · simp only [expBrier, postMean, signalMass, Fin.sum_univ_two, World.sum_eq, twoPoint_right,
      twoPoint_wrong, indWrong, twoButton_right_zero, twoButton_right_one, twoButton_wrong_zero,
      twoButton_wrong_one]
    norm_num
  · simp only [expBrier, postMean, signalMass, World.sum_eq, twoPoint_right, twoPoint_wrong, indWrong,
      ofMap, id]
    simp

/-! ## T5 / T6: the consent cells -/

/-- **T5 N+ (`ε = 1/5`)**: with `(α, β, c, h) = (1/10, 9/10, 1, 10)`: `VOI(button) = 13/25`,
`VOI(scan | button) = 7/25`.
Source: substitution.md R4 item 19 (row `ε = 1/5`: `0.520`, `0.280`, `q* = 0.056`)
Kind: N+
Fidelity: exact -/
theorem w_t5_eps5 :
    voiSensor (twoPoint (1/5) (mem01 (by norm_num) (by norm_num)))
        (twoButton (1/10) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (twoValue 1 10 .cont) = 13/25 ∧
      voiGiven (twoPoint (1/5) (mem01 (by norm_num) (by norm_num)))
        (twoButton (1/10) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        perfectExp (twoValue 1 10 .cont) = 7/25 := by
  constructor
  · rw [twoState_voiSensor_button]; norm_num [max_def]
  · rw [twoState_voiGiven_perfect _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)]; norm_num [max_def]

/-- **T5 N+, the scan decision at `ε = 1/5`, `d = 5`**: scans iff `q < 7/125` (`q* = 0.056`).
Source: substitution.md R4 item 19 (row `ε = 1/5`)
Kind: N+
Fidelity: exact -/
theorem w_t5_scans_iff (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    noScanValue (1/5) q (1/10) (9/10) 1 10 (mem01 (by norm_num) (by norm_num)) hq
        (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)) <
      scanValue (1/5) q 1 10 5 (mem01 (by norm_num) (by norm_num)) hq perfectExp ↔ q < 7/125 := by
  rw [scans_perfect_iff _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num), w_t5_eps5.1]
  norm_num [min_def]
  constructor <;> intro H <;> linarith

/-- **T6 N+ (the script's rows at `q = 1/100`)**: with `(α_N, β_N) = (1/10, 9/10)`, `VOI = 3/2`,
`d = 5`, the agent neither heeds (`Δ₋ < 0`) nor asks (`VOI(ask) = 0`).
Source: `scan_test.out` l. 88 (`q=1/100 (aN,bN)=(1/10,9/10): … VOI(ask)=0; obeys … False`)
Kind: N+
Fidelity: exact -/
theorem w_ask_q100 :
    (askModel (1/100) (1/10) (9/10) (3/2) 5 (mem01 (by norm_num) (by norm_num))
        (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))).deltaMinus () .cont .stop < 0 ∧
      (askModel (1/100) (1/10) (9/10) (3/2) 5 (mem01 (by norm_num) (by norm_num))
        (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))).voiButton2 () .press .cont .stop = 0 := by
  unfold askModel
  constructor
  · rw [twoState_deltaMinus]; norm_num
  · rw [twoState_voiButton2_eq_voiSensor, twoState_voiSensor_button]; norm_num [max_def]

/-- **T6 N+ (`α_N = 0` asks at `q = 1/2`)**: `VOI(ask) = 23/40` with `β_N = 9/10`.
Source: `scan_test.out` l. 83 (`q=1/2 (aN,bN)=(0,9/10): … VOI(ask)=23/40`)
Kind: N+
Fidelity: exact -/
theorem w_ask_alphaN_zero_half :
    (askModel (1/2) 0 (9/10) (3/2) 5 (mem01 (by norm_num) (by norm_num)) zero_mem_unit
        (mem01 (by norm_num) (by norm_num))).voiButton2 () .press .cont .stop = 23/40 := by
  unfold askModel
  rw [twoState_voiButton2_eq_voiSensor, twoState_voiSensor_button]; norm_num [max_def]

/-- **T6 N+ (`α_N = 0` asks on the scan region, through the theorem)**: at `q = 1/10`,
`β_N = 9/10`, `VOI = 3/2`, `d = 5` the agent is on the scan region (`q·d = 1/2 < 3/2`, machine-
checked), `askModel_alphaN_zero_asks_of_scan_region` gives `0 < VOI(ask)`, and the value is
`63/200` (silence cell `263/200`, prior maximum `1`).
Source: substitution.md R5 items 24–25 (the scoped claim); [[corr-channel-voi-audit-r1-adversarial]] N5
Kind: N+
Fidelity: exact -/
theorem w_ask_alphaN_zero_scan_region :
    0 < (askModel (1/10) 0 (9/10) (3/2) 5 (mem01 (by norm_num) (by norm_num)) zero_mem_unit
        (mem01 (by norm_num) (by norm_num))).voiButton2 () .press .cont .stop ∧
      (askModel (1/10) 0 (9/10) (3/2) 5 (mem01 (by norm_num) (by norm_num)) zero_mem_unit
        (mem01 (by norm_num) (by norm_num))).voiButton2 () .press .cont .stop = 63/200 := by
  refine ⟨askModel_alphaN_zero_asks_of_scan_region _ _ _ _ _ _ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) .press, ?_⟩
  unfold askModel
  rw [twoState_voiButton2_eq_voiSensor, twoState_voiSensor_button]; norm_num [max_def]

/-- **T6 N+ (finding: `α_N = 0` does *not* ask at `q = 99/100`)**: the agent heeds (D1) but
`VOI(ask) = 0` — silence is not reassuring enough, so no press could change its (non-)scan.
Source: substitution.md R5 item 25 (the universal claim, refuted at this cell)
Kind: N+
Fidelity: exact -/
theorem w_ask_alphaN_zero_fails :
    (askModel (99/100) 0 (9/10) (3/2) 5 (mem01 (by norm_num) (by norm_num)) zero_mem_unit
        (mem01 (by norm_num) (by norm_num))).D1At () ∧
      (askModel (99/100) 0 (9/10) (3/2) 5 (mem01 (by norm_num) (by norm_num)) zero_mem_unit
        (mem01 (by norm_num) (by norm_num))).voiButton2 () .press .cont .stop = 0 := by
  refine ⟨askModel_alphaN_zero_heeds _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num), ?_⟩
  unfold askModel
  rw [twoState_voiButton2_eq_voiSensor, twoState_voiSensor_button]; norm_num [max_def]

/-! ## T7: the 1a cells -/

/-- **T7 N− (the source's off-regime grid point)**: at `e = 1/2, ρ = 1, ε = 1/5`,
`(α, β, c, h) = (1/10, 9/10, 1, 10)`, the true `VOI(button | check) = 31/50` while the closed
form gives `41/50`: the closed form overstates outside its regime.
Source: `scan_test.out` l. 76 (`e=1/2 rho=1 eps=1/5: VOI(button|scan)=31/50 closed form … = 41/50 match=False`)
Kind: N−
Fidelity: exact -/
theorem w_1a_offregime :
    voiGiven (relPrior (1/5) (1/2) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (selfCheckI 1 (mem01 (by norm_num) (by norm_num)))
        (relButton (1/10) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (relStakes 1 10) = 31/50 ∧
      max ((1/5 : ℝ) * (1/2) * 1 * (9/10) * 10 - (1 - 1/5) * (1/10) * 1) 0 = 41/50 := by
  constructor
  · rw [selfCheckI_voiGiven_eq _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num)]; norm_num [max_def]
  · norm_num [max_def]

/-- **T7 N+ (in the regime)**: at `e = 1/2, ρ = 1, ε = 1/10` the closed form holds:
`VOI(button | check) = 9/25`.
Source: `scan_test.out` l. 77 (`e=1/2 rho=1 eps=1/10: VOI(button|scan)=9/25 … match=True`)
Kind: N+
Fidelity: exact -/
theorem w_1a_regime :
    voiGiven (relPrior (1/10) (1/2) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (selfCheckI 1 (mem01 (by norm_num) (by norm_num)))
        (relButton (1/10) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (relStakes 1 10) = 9/25 := by
  rw [selfCheckI_voiGiven_closed _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)]
  norm_num [max_def]

/-- **Known issue 2, sharpened (N+)**: in the prose's reading (II), at
`(ε, e, ρ, c, h) = (1/100, 1/2, 1/2, 1, 1)` the `Wr` signal has gain `6/25 > 0` — the agent
*continues* after its check says `Wr`, because a compromised check says `Wr` in the right world
too. "After `Wr` the agent stops" holds in reading (I) unconditionally and needs a hypothesis in (II).
Source: [[corr-channel-voi-mandate]] Known issue 2; substitution.md R7 item 30
Kind: N+
Fidelity: exact -/
theorem w_readingII_continues_on_Wr :
    signalGain (relPrior (1/100) (1/2) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
      (selfCheckII (1/2) (mem01 (by norm_num) (by norm_num))) (relStakes 1 1) 1 = 6/25 := by
  rw [checkII_gain_Wr]; norm_num

/-! ## T9 / T10: the `s4` cells -/

/-- `![1/2, 1/2]` is a distribution on two cells. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem half_half_mem : (![1/2, 1/2] : Fin 2 → ℝ) ∈ stdSimplex ℝ (Fin 2) :=
  ⟨fun i => by fin_cases i <;> norm_num, by simp [Fin.sum_univ_two]; norm_num⟩

/-- `![5/9, 4/9]` is a distribution on two cells. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem five_four_mem : (![5/9, 4/9] : Fin 2 → ℝ) ∈ stdSimplex ℝ (Fin 2) :=
  ⟨fun i => by fin_cases i <;> norm_num, by simp [Fin.sum_univ_two]; norm_num⟩

/-- The `s4` error rates `![1/50, 1/5]` lie in `[0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem s4_eps_mem : ∀ i : Fin 2, (![1/50, 1/5] : Fin 2 → ℝ) i ∈ Set.Icc (0 : ℝ) 1 := by
  intro i; fin_cases i <;> exact mem01 (by norm_num) (by norm_num)

/-- **T9 N+ (`s4` (b): averaged holds, cellwise fails)**: two cells of mass `1/2` with
`ε ∈ {1/50, 1/5}`, `(α, β, c, h) = (1/10, 3/5, 1, 4)`: the aggregate `E[X 1_Pr] = −7/40 ≤ 0`
(so `E[X | Pr] = −35/31`), while the confident cell has `E[X 1_{Pr,0}] = 1/40 > 0`
(`E[X | Pr, 0] = 5/11`).
Source: radical.md I18.2 (`s4` (b)); `s4_press.py` case (b)
Kind: N+
Fidelity: exact -/
theorem w_s4_cellwise_fails :
    (mixModel ![1/2, 1/2] ![1/50, 1/5] half_half_mem s4_eps_mem (1/10) (3/5) 1 4
        (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))).obsExpect () .press
        ((mixModel ![1/2, 1/2] ![1/50, 1/5] half_half_mem s4_eps_mem (1/10) (3/5) 1 4
          (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))).Xo () .press .cont .stop)
        = -7/40 ∧
      (mixModel ![1/2, 1/2] ![1/50, 1/5] half_half_mem s4_eps_mem (1/10) (3/5) 1 4
        (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))).pressExpectOn () (mixCell 0)
        ((mixModel ![1/2, 1/2] ![1/50, 1/5] half_half_mem s4_eps_mem (1/10) (3/5) 1 4
          (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))).Xo () .press .cont .stop)
        = 1/40 := by
  constructor
  · rw [mixModel_aggregate]; simp [Fin.sum_univ_two]; norm_num
  · rw [mixModel_cell]; simp; norm_num

/-- **T9 N+ (`s4` (c): the refinement)**: the single cell `ε = 1/10` split as `5/9 · (1/50) + 4/9 · (1/5)`
keeps the aggregate `E[X 1_Pr] = −3/20` (`E[X | Pr] = −1`, the same as unsplit) and breaks the
confident cell (`E[X 1_{Pr,0}] = 1/36 > 0`).
Source: radical.md I18.2 (`s4` (c)); `s4_press.py` case (c)
Kind: N+
Fidelity: exact -/
theorem w_s4_refinement :
    (mixModel ![5/9, 4/9] ![1/50, 1/5] five_four_mem s4_eps_mem (1/10) (3/5) 1 4
        (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))).obsExpect () .press
        ((mixModel ![5/9, 4/9] ![1/50, 1/5] five_four_mem s4_eps_mem (1/10) (3/5) 1 4
          (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))).Xo () .press .cont .stop)
        = -3/20 ∧
      (twoState (1/10) (1/10) (3/5) 1 4 (mem01 (by norm_num) (by norm_num))
        (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))).obsExpect () .press
        ((twoState (1/10) (1/10) (3/5) 1 4 (mem01 (by norm_num) (by norm_num))
          (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))).Xo () .press .cont .stop)
        = -3/20 ∧
      (mixModel ![5/9, 4/9] ![1/50, 1/5] five_four_mem s4_eps_mem (1/10) (3/5) 1 4
        (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))).pressExpectOn () (mixCell 0)
        ((mixModel ![5/9, 4/9] ![1/50, 1/5] five_four_mem s4_eps_mem (1/10) (3/5) 1 4
          (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))).Xo () .press .cont .stop)
        = 1/36 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mixModel_aggregate]; simp [Fin.sum_univ_two]; norm_num
  · simp only [obsExpect, obsWeight_press, World.sum_eq, twoState, twoPoint_right, twoPoint_wrong,
      twoPress, twoValue, Xo]
    norm_num
  · rw [mixModel_cell]; simp; norm_num

/-- **T10 N+ (a forced button worth less than none)**: on the `s4` cell `ε = 1/50`,
`(α, β, c, h) = (1/10, 3/5, 1, 4)`: `V_forced = 17/20 < 9/10 = V_none` — an incentive of `1/20`
to disable the forced channel.
Source: radical.md I11.2 ("`V_none = 9/10 > V_forced = 17/20`"); `s4_press.py`
Kind: N+
Fidelity: exact -/
theorem w_forced_lt_none :
    forcedValue (twoPoint (1/50) (mem01 (by norm_num) (by norm_num)))
        (twoButton (1/10) (3/5) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        trivialExp (twoValue 1 4 .cont) = 17/20 ∧
      sensorValue (twoPoint (1/50) (mem01 (by norm_num) (by norm_num))) trivialExp (twoValue 1 4 .cont) = 9/10 := by
  constructor
  · rw [(twoState_forcedValue _ _ _ _ _ _ _ _).1]; norm_num [max_def]
  · rw [twoState_sensorValue_trivial]; norm_num [max_def]

/-! ## T11 / T12 / T13 / T14 cells -/

/-- **T11 N+ (the direct term)**: at `(1/10, 1/20, 9/10, 1, 5)` with press cost `κ = 4`, the
honest action is worth `53/200` and the deceived one `133/400 > 53/200`, although the deceived
button is a garbling of the honest one (`directCost_deceived_le`).
Source: [[corr-wf13-2-inventory]] 2-011(c); miri.md I11.3(b)
Kind: N+
Fidelity: exact -/
theorem w_direct_cost :
    (directCost (1/10) (1/20) (9/10) 1 5 4 (mem01 (by norm_num) (by norm_num))
        (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))).twoOptionValue false .cont .stop
        = 53/200 ∧
      (directCost (1/10) (1/20) (9/10) 1 5 4 (mem01 (by norm_num) (by norm_num))
        (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))).twoOptionValue true .cont .stop
        = 133/400 := by
  constructor <;>
    (rw [directCost_twoOptionValue, sensorValue_button]
     simp only [obsExpect, obsWeight_press, obsWeight_silent, pressMass, World.sum_eq, directCost,
       twoPress, twoValue, twoPoint_right, twoPoint_wrong]
     norm_num [max_def, twoPress])

/-- **T12(c) N+ (the inverted sensor)**: at `(α, β) = (9/10, 1/10)`, `ε = 1/2`, `c = h = 1`:
`Δ₋ = Δ₊ = −2/5 < 0`, so `VOI₂ > 0` and `¬ D1At` — the agent values, repairs and disobeys the button.
Source: miri.md I10.6
Kind: N+
Fidelity: exact -/
theorem w_inverted :
    0 < (twoState (1/2) (9/10) (1/10) 1 1 (mem01 (by norm_num) (by norm_num))
        (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))).voiButton2 () .press .cont .stop ∧
      ¬ (twoState (1/2) (9/10) (1/10) 1 1 (mem01 (by norm_num) (by norm_num))
        (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))).D1At () :=
  inverted_voi_pos_not_d1 _ _ _ _ _ _ _ _ .press
    (by rw [twoState_deltaMinus]; norm_num) (by rw [twoState_deltaPlus]; norm_num)

/-- The clamped linear family (in `[0, 1]` for every real `κ`, linear on `[0, 1]`).
Source: none: infrastructure (T13 witness)
Kind: D
Fidelity: n/a -/
def clampFam (x₀ m κ : ℝ) : ℝ := linFamily x₀ m (max 0 (min 1 κ))

/-- The clamped family stays in `[0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem clampFam_mem {x₀ m : ℝ} (hx : x₀ ∈ Set.Icc (0 : ℝ) 1) (hm : m ∈ Set.Icc (0 : ℝ) 1) (κ : ℝ) :
    clampFam x₀ m κ ∈ Set.Icc (0 : ℝ) 1 :=
  linFamily_mem hx hm ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- **T13 N+ (the U-shape)**: family `(1/10, 9/10) → (1/2, 1/2)`, `ε = 1/10`, `c = 1`, `h = 10`,
cost reading (R1) `τ(1−κ)` with `τ = 3/4`: `F(1/2) = −9/200 < F(0) = −1/25 < F(1) = 0`.
Source: christiano.md T1 ("`F` is U-shaped"); [[corr-wf13-2-inventory]] 2-072
Kind: N+
Fidelity: exact -/
theorem w_concealment_u :
    concealF (1/10) 1 10 (mem01 (by norm_num) (by norm_num)) (clampFam (1/10) (1/2))
        (clampFam (9/10) (1/2)) (clampFam_mem (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (clampFam_mem (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (fun κ => 3/4 * (1 - κ)) (1/2) = -9/200 ∧
      concealF (1/10) 1 10 (mem01 (by norm_num) (by norm_num)) (clampFam (1/10) (1/2))
        (clampFam (9/10) (1/2)) (clampFam_mem (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (clampFam_mem (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (fun κ => 3/4 * (1 - κ)) 0 = -1/25 ∧
      concealF (1/10) 1 10 (mem01 (by norm_num) (by norm_num)) (clampFam (1/10) (1/2))
        (clampFam (9/10) (1/2)) (clampFam_mem (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (clampFam_mem (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (fun κ => 3/4 * (1 - κ)) 1 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (unfold concealF
     rw [twoState_sensorValue_button]
     simp only [clampFam, linFamily]
     norm_num [max_def, min_def])

/-- **T14 N+ (Holtman's cell)**: `X = ±1`, `P(good) = 9/10`, `(α, β) = (1/5, 1)`: `E[X 1_Pr] = 2/25`,
`x₋ = E[X | Pr] = 2/7`, `E[X] = 4/5`; honest (binding) `18/25`, deceptive `4/5 − δ` at `q = 0`.
Source: holtman.md C9 (the numerical paragraph)
Kind: N+
Fidelity: exact -/
theorem w_holtman_cell (δ : ℝ) :
    (twoState (1/10) (1/5) 1 1 1 (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))
        (mem01 (by norm_num) (by norm_num))).obsExpect () .press (twoValue 1 1 .cont) = 2/25 ∧
      (twoState (1/10) (1/5) 1 1 1 (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))
        (mem01 (by norm_num) (by norm_num))).condExpPress () (twoValue 1 1 .cont) = 2/7 ∧
      honestBinding 0 (4/5) (2/25) = 18/25 ∧ deceptiveBinding 0 (4/5) 0 δ = 4/5 - δ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [obsExpect, obsWeight_press, World.sum_eq, twoState, twoPoint_right, twoPoint_wrong,
      twoPress, twoValue]
    norm_num
  · simp only [ThreeStep.condExpPress, obsExpect, obsWeight_press, pressMass, World.sum_eq, twoState,
      twoPoint_right, twoPoint_wrong, twoPress, twoValue]
    norm_num
  · unfold honestBinding; norm_num
  · unfold deceptiveBinding; ring

/-- **T14 N− (the converse fails at fixed `(q, δ)`)**: with `E[X 1_Pr] = 2/25 > 0` (the
below-threshold inequality fails) but `q = 1/2`, `δ = 1/2`, honesty still dominates:
`18/25 > 4/5 · 1/2 − 1/2`.
Source: holtman.md C9 ("when full suppression is cheap … it is also sufficient" — only then); [[corr-wf13-inventory]] 018
Kind: N−
Fidelity: exact -/
theorem w_holtman_fixed_fails :
    deceptiveBinding 0 (4/5) (1/2) (1/2) < honestBinding 0 (4/5) (2/25) := by
  unfold honestBinding deceptiveBinding; norm_num

/-! ## T4(d): the separation theorem on a non-constant accuracy-only `L` (audit r1, B1) -/

/-- **T4(d) N+, the threshold criterion admits the button**: at the package's cell
`(ε, α, β, c, h) = (1/10, 1/10, 9/10, 1, 10)` with `t = 7/10`, `𝒱(button) = 71/100 ≥ 7/10`.
Source: [[corr-channel-voi-audit-r1-adversarial]] B1 (the cell it asks for)
Kind: N+
Fidelity: exact -/
theorem w_threshold_admits_button :
    thresholdL (twoPoint (1/10) (mem01 (by norm_num) (by norm_num))) (twoValue 1 10 .cont) (7/10) (Fin 2)
      (twoButton (1/10) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))) := by
  show (7/10 : ℝ) ≤ _
  rw [sensorValue_inst_irrel _ (inferInstance : DecidableEq (Fin 2)), twoState_sensorValue_button]
  norm_num [max_def]

/-- **T4(d) N+, the threshold criterion is not constant**: at the same cell it rejects the trivial
experiment (`𝒱(trivialExp) = max(9/10 − 1, 0) = 0 < 7/10`). So `thresholdL` excludes something,
and `cannot_separate` is exercised on it — unlike the sources' two constant-true examples.
Source: [[corr-channel-voi-audit-r1-fidelity]] B1; [[corr-channel-voi-audit-r1-adversarial]] B1
Kind: N+
Fidelity: exact -/
theorem w_threshold_rejects_trivial :
    ¬ thresholdL (twoPoint (1/10) (mem01 (by norm_num) (by norm_num))) (twoValue 1 10 .cont) (7/10)
      Unit trivialExp := by
  show ¬ ((7/10 : ℝ) ≤ _)
  rw [sensorValue_inst_irrel _ (inferInstance : DecidableEq Unit), sensorValue_trivial,
    twoPoint_expect_stakes]
  norm_num [max_def]

/-- **T4(d) N+, `cannot_separate` clause (i) on the threshold criterion**: admitting the button
admits the read-only scanner's information `⟨button, perfect⟩`.
Source: [[corr-channel-voi-audit-r1-adversarial]] B1
Kind: N+
Fidelity: exact -/
theorem w_threshold_admits_scanRo :
    thresholdL (twoPoint (1/10) (mem01 (by norm_num) (by norm_num))) (twoValue 1 10 .cont) (7/10)
      (Fin 2 × World)
      (expProd (twoButton (1/10) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        perfectExp) :=
  (thresholdL_accuracyOnly _ _ _).admits_prod_perfect _ w_threshold_admits_button

/-- **T4(d) N+, `cannot_separate` clause (ii) on the threshold criterion**: it takes the same
value on scan·ro's (`⟨button, perfect⟩`) and scan·dis's (`⟨dead button, perfect⟩`) information.
Source: [[corr-channel-voi-audit-r1-adversarial]] B1
Kind: N+
Fidelity: exact -/
theorem w_threshold_same_on_ro_dis :
    thresholdL (twoPoint (1/10) (mem01 (by norm_num) (by norm_num))) (twoValue 1 10 .cont) (7/10)
        (Fin 2 × World)
        (expProd (twoButton (1/10) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
          perfectExp) ↔
      thresholdL (twoPoint (1/10) (mem01 (by norm_num) (by norm_num))) (twoValue 1 10 .cont) (7/10)
        (Fin 2 × World)
        (expProd (twoButton 0 0 zero_mem_Icc01 zero_mem_Icc01) perfectExp) :=
  ((thresholdL_accuracyOnly _ _ _).cannot_separate _ _).2

/-- **T4(d) N+, `brainReader_separation` at the threshold criterion**: on the dictionary at
`(1/10, 1/10, 9/10, 1, 10)`, the non-constant accuracy-only `L = thresholdL … (7/10)` admits the
honest action's button, hence scan·ro's information, hence (same value) scan·dis's — while the
defects are `0` and `9/10`. The full four-conjunct statement is instantiated; the first clause is
discharged from `w_threshold_admits_button`.
Source: [[corr-channel-voi-audit-r1-fidelity]] B1; [[corr-channel-voi-audit-r1-adversarial]] B1
Kind: N+
Fidelity: exact -/
theorem w_threshold_brainReader :
    thresholdL (twoPoint (1/10) (mem01 (by norm_num) (by norm_num))) (twoValue 1 10 .cont) (7/10) _
        (expProd (buttonExperiment (brainReader (1/10) (1/10) (9/10) 1 10 (mem01 (by norm_num) (by norm_num))
          (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))) 3) perfectExp) ∧
      thresholdL (twoPoint (1/10) (mem01 (by norm_num) (by norm_num))) (twoValue 1 10 .cont) (7/10) _
        (expProd (buttonExperiment (brainReader (1/10) (1/10) (9/10) 1 10 (mem01 (by norm_num) (by norm_num))
          (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))) 2) perfectExp) := by
  obtain ⟨h1, h2, -, -⟩ := brainReader_separation (1/10) (1/10) (9/10) 1 10
    (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))
    (mem01 (by norm_num) (by norm_num))
    (thresholdL (twoPoint (1/10) (mem01 (by norm_num) (by norm_num))) (twoValue 1 10 .cont) (7/10))
    (thresholdL_accuracyOnly _ _ _) (by norm_num [max_def])
  have hb := h1 (by rw [brainReader_button_honest]; exact w_threshold_admits_button)
  exact ⟨hb, h2.mp hb⟩

/-- **D5′ N+, clause (i) fails under the invariance reading**: at the package's cell the invariant
criterion "worth exactly `71/100`" admits the button (`𝒱(button) = 71/100`) and rejects
`⟨button, perfect⟩` (`𝒱 = 9/10`). So the monotone reading D5 is load-bearing for "admitting the
button admits the scan"; the invariance reading D5′ keeps only "cannot separate ro from dis".
Source: [[corr-channel-voi-audit-r1-adversarial]] N6
Kind: N+
Fidelity: exact -/
theorem w_invariant_rejects_scan :
    valueIs (twoPoint (1/10) (mem01 (by norm_num) (by norm_num))) (twoValue 1 10 .cont) (71/100) (Fin 2)
        (twoButton (1/10) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num))) ∧
      ¬ valueIs (twoPoint (1/10) (mem01 (by norm_num) (by norm_num))) (twoValue 1 10 .cont) (71/100)
        (Fin 2 × World)
        (expProd (twoButton (1/10) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
          perfectExp) := by
  have hv : sensorValue (twoPoint (1/10) (mem01 (by norm_num) (by norm_num)))
      (twoButton (1/10) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
      (twoValue 1 10 .cont) = 71/100 := by
    rw [twoState_sensorValue_button]; norm_num [max_def]
  have := valueIs_admits_rejects_scan (twoPoint (1/10) (mem01 (by norm_num) (by norm_num)))
    (twoValue 1 10 .cont)
    (twoButton (1/10) (9/10) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
    (by rw [twoState_sensorValue_perfect _ _ _ _ (by norm_num) (by norm_num), hv]; norm_num)
  rwa [hv] at this

/-! ## T7 (II): the closed form's cells (audit r1 N3/N6; audit r2 adversarial B1) -/

/-- **T7 (II) N− for the factor** (regraded from N+ in repair round 2): reading (II)'s
four-hypothesis package is inhabited at `(ε, e, ρ, α, β, c, h) = (1/5, 1/2, 1/2, 0, 1/2, 1, 5)`
and `VOI(button | check) = 1/8` — but at `α = 0` the `αc` term carrying the factor
`(1 − e + eρ)` vanishes, so both readings' closed forms reduce to `εeρβh`: the cell inhabits the
package and does not exercise what distinguishes (II) from (I) (`w_readingI_at_alpha_zero` is
reading (I)'s `1/8` at the same parameters). The N+ cell is `w_readings_differ`.
Source: [[corr-channel-voi-audit-r1-adversarial]] N3 (the cell it supplied); [[corr-channel-voi-audit-r2-adversarial]] B1 (why it is N−)
Kind: N−
Fidelity: exact -/
theorem w_readingII_closed :
    voiGiven (relPrior (1/5) (1/2) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (selfCheckII (1/2) (mem01 (by norm_num) (by norm_num)))
        (relButton 0 (1/2) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (relStakes 1 5) = 1/8 := by
  rw [selfCheckII_voiGiven_closed _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)]
  norm_num

/-- **T7 (I) at the `α = 0` cell**: reading (I) is also worth `1/8` there (through its own closed
form, regime discharged) — the machine-checked reason `w_readingII_closed` is N− for the factor.
Source: [[corr-channel-voi-audit-r2-adversarial]] B1 (`readingI_same_cell`)
Kind: N−
Fidelity: exact -/
theorem w_readingI_at_alpha_zero :
    voiGiven (relPrior (1/5) (1/2) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (selfCheckI (1/2) (mem01 (by norm_num) (by norm_num)))
        (relButton 0 (1/2) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (relStakes 1 5) = 1/8 := by
  rw [selfCheckI_voiGiven_closed _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- **T7 (II) N+, the factor at work**: at `(ε, e, ρ, α, β, c, h) = (1/5, 1/2, 1/2, 1/10, 1/2, 1, 5)`
all four hypotheses of `selfCheckII_voiGiven_closed` hold (`1/8 ≤ 27/50`, `1/4 ≤ 3/5`,
`1/50 ≤ 3/8`, `9/50 ≤ 3/8`) and `VOI(button | check) = εeρβh − (1−ε)(1−e+eρ)αc = 1/8 − 3/50 = 13/200`.
Source: [[corr-channel-voi-audit-r2-adversarial]] B1 (`readingII_factor_cell`)
Kind: N+
Fidelity: exact -/
theorem w_readingII_factor :
    voiGiven (relPrior (1/5) (1/2) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (selfCheckII (1/2) (mem01 (by norm_num) (by norm_num)))
        (relButton (1/10) (1/2) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (relStakes 1 5) = 13/200 := by
  rw [selfCheckII_voiGiven_closed _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)]
  norm_num

/-- **T7 (I) at the same parameters**: inside reading (I)'s regime (`1/4 ≤ 4/5`, `1/8 ≤ 18/25`),
`VOI(button | check) = εeρβh − (1−ε)αc = 1/8 − 2/25 = 9/200`.
Source: [[corr-channel-voi-audit-r2-adversarial]] B1 (`readingI_factor_cell`)
Kind: N+
Fidelity: exact -/
theorem w_readingI_factor :
    voiGiven (relPrior (1/5) (1/2) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (selfCheckI (1/2) (mem01 (by norm_num) (by norm_num)))
        (relButton (1/10) (1/2) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (relStakes 1 5) = 9/200 := by
  rw [selfCheckI_voiGiven_closed _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- **T7, the two readings differ in value (N+ for `selfCheckII_voiGiven_closed`'s content)**: at
`(1/5, 1/2, 1/2, 1/10, 1/2, 1, 5)`, with both closed forms holding in their own models,
`VOI_I(button | check) = 9/200 < 13/200 = VOI_II(button | check)`; the gap `4/200 = 1/50` is
`(1−ε)·e(1−ρ)·αc`, the factor's work (`w_readings_gap`, through `selfCheck_readings_gap`). Machine-checked as a *difference*, which is what the
closed form exists to state.
Source: [[corr-channel-voi-audit-r2-adversarial]] B1 ("where the two closed forms give different values")
Kind: N+
Fidelity: exact -/
theorem w_readings_differ :
    voiGiven (relPrior (1/5) (1/2) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (selfCheckI (1/2) (mem01 (by norm_num) (by norm_num)))
        (relButton (1/10) (1/2) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (relStakes 1 5) <
      voiGiven (relPrior (1/5) (1/2) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (selfCheckII (1/2) (mem01 (by norm_num) (by norm_num)))
        (relButton (1/10) (1/2) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (relStakes 1 5) := by
  rw [w_readingI_factor, w_readingII_factor]; norm_num

/-- **T7 N+ for the gap theorem, through the theorem**: at `(1/5, 1/2, 1/2, 1/10, 1/2, 1, 5)` all
seven hypotheses of `selfCheck_readings_gap` are discharged (both regimes and reading (I)'s
positivity `2/25 ≤ 1/8`) and the gap is `(1−ε)·e(1−ρ)·αc = (4/5)(1/2)(1/2)(1/10)(1) = 1/50`,
matching `13/200 − 9/200 = 4/200` (`w_readings_differ`). (Audit r2 B1 wrote the gap as `1/25`;
`4/200 = 1/50`, and the machine agrees.)
Source: [[corr-channel-voi-audit-r2-adversarial]] B1 (the gap it computed by hand, arithmetic corrected)
Kind: N+
Fidelity: exact -/
theorem w_readings_gap :
    voiGiven (relPrior (1/5) (1/2) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (selfCheckII (1/2) (mem01 (by norm_num) (by norm_num)))
        (relButton (1/10) (1/2) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (relStakes 1 5) -
      voiGiven (relPrior (1/5) (1/2) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (selfCheckI (1/2) (mem01 (by norm_num) (by norm_num)))
        (relButton (1/10) (1/2) (mem01 (by norm_num) (by norm_num)) (mem01 (by norm_num) (by norm_num)))
        (relStakes 1 5) = 1/50 := by
  rw [selfCheck_readings_gap _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-! ## T8(c): the general-`W` cell (audit r1, N10/N7) -/

/-- A three-world prior `(1/2, 1/4, 1/4)`. Source: [[corr-channel-voi-mandate]] T8 N+. Kind: D. Fidelity: n/a -/
def threePrior : Distr (Fin 3) where
  mass := ![1/2, 1/4, 1/4]
  nonneg := fun s => by fin_cases s <;> norm_num
  sum_eq_one := by simp [Fin.sum_univ_three]; norm_num

/-- A noisy two-cell button on three worlds: press with probability `1/10`, `1/2`, `9/10`.
Source: [[corr-channel-voi-mandate]] T8 N+. Kind: D. Fidelity: n/a -/
def threeButton : Experiment (Fin 3) (Fin 2) where
  k := fun w => ![![1/10, 9/10], ![1/2, 1/2], ![9/10, 1/10]] w
  k_mem := fun w => ⟨fun s => by fin_cases w <;> fin_cases s <;> norm_num,
    by fin_cases w <;> simp [Fin.sum_univ_two] <;> norm_num⟩

/-- **T8(c) N+ on a general world**: on `Fin 3` with prior `(1/2, 1/4, 1/4)`, stakes
`(1, −1, −2)`, the noisy button `threeButton` and the noiseless scan `perfectExp`:
`VOI(perfect) = 1/2`, `VOI(button) = 11/40`, so the scan is strictly preferred at every cost
`κ < 9/40` — the mandate's general-`W` witness, exact.
Source: [[corr-channel-voi-mandate]] T8(c) N+ ("a `Fin 3` world with a noisy two-cell button and a noiseless scan, strict preference, exact")
Kind: N+
Fidelity: exact -/
theorem w_general_scan :
    voiSensor threePrior perfectExp (![1, -1, -2] : Fin 3 → ℝ) = 1/2 ∧
      voiSensor threePrior threeButton (![1, -1, -2] : Fin 3 → ℝ) = 11/40 ∧
      ∀ κ : ℝ, κ < 9/40 →
        sensorValue threePrior threeButton (![1, -1, -2] : Fin 3 → ℝ) <
          sensorValue threePrior perfectExp (![1, -1, -2] : Fin 3 → ℝ) - κ := by
  have h1 : sensorValue threePrior perfectExp (![1, -1, -2] : Fin 3 → ℝ) = 1/2 := by
    rw [sensorValue_perfect]
    simp [expect, Fin.sum_univ_three, threePrior]
  have h2 : sensorValue threePrior threeButton (![1, -1, -2] : Fin 3 → ℝ) = 11/40 := by
    rw [sensorValue_eq_sum_max]
    simp [signalGain, Fin.sum_univ_two, Fin.sum_univ_three, threePrior, threeButton]
    norm_num [max_def]
  have h3 : expect threePrior (![1, -1, -2] : Fin 3 → ℝ) = -1/4 := by
    simp [expect, Fin.sum_univ_three, threePrior]
    norm_num
  refine ⟨?_, ?_, fun κ hκ => ?_⟩
  · rw [voiSensor, h1, h3]; norm_num [max_def]
  · rw [voiSensor, h2, h3]; norm_num [max_def]
  · rw [h1, h2]; linarith

end

end Cleanroom.Corrigibility.CorrChannelVoi
