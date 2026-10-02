import Cleanroom.Decision.DpCalibration.Limit
import Cleanroom.Decision.DpLearnerNr.TbThetaDoc

/-!
# `dp-learner-nr` target 2: tremble swamping in closed form, and its absence on the doc-faithful tree

On `dp-causal-consist`'s bypass `tbTheta θ` with the trembled label `C := tremble (procQ q) ε`
(Definition 10's `C^ε`, `dp-calibration`'s `tremble`: `(1−ε)·C(d) + ε·Unif`, so the trembled
crossing weight is `w := (1−ε)q + ε/2`, `tremble_procQ_w`):

* `tb_tremble_pBot`: `P(bot ∣ cross-event) = θ / (θ + (1−θ)·w)`; at the stay label `q = 0` this is
  `θ/(θ + (1−θ)ε/2)` (`tb_tremble_stay_pBot`), at the cross label `θ/(θ + (1−θ)(1 − ε/2))`
  (`tb_tremble_cross_pBot`);
* `tb_tremble_value`: the evidential value of crossing is `10 − 20·P(bot ∣ cross)`;
* `tb_tremble_stay_swamped`: as `ε → 0` the stay-label conditional exceeds `1 − δ` and the value
  drops below `−10 + 20δ` (explicit `ε₀ := δθ`); `tb_tremble_stay_neg` re-founds dp-sl-2-071's
  `tremble_neg` over `tbTheta`: the value is negative for `0 < ε < 2θ/(1−θ)`;
* the deviation gap `10(1−θ)` is `ε`-free (`tb_tremble_dev_gap`, `tb_dev_gap` cited);
* `p11_regression`: the five P11 numerals as instances of `tb_condExp_cross`/`tb_stay_condExp`.

**Then on the doc-faithful tree** (`tbThetaDoc_tremble_pBot`, `tbThetaDoc_tremble_value`): at
every label and every `ε > 0`, `P(bot ∣ cross-event) = θ` and the value of crossing is
`10 − 20θ` — crossing has no forced mass, so nothing is swamped. `swamping_contrast` states the
pair under one hypothesis package: the swamping is bypass-specific (findings, severity
imprecision against [[tb-theta-shadow]] "the troll punishes exploration is reproduced").
-/

namespace Cleanroom.Decision.DpLearnerNr

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Found.DpCoreTree.Catalogue
  Cleanroom.Decision.DpCalibration Cleanroom.Decision.DpCausalConsist Finset

/-- `Fintype.card Act2 = 2`. Source: none: infrastructure. Kind: L -/
theorem card_act2 : Fintype.card Act2 = 2 := by decide

section bypass

variable (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (ε : ℚ) (e0 : 0 ≤ ε) (e1 : ε ≤ 1)
  (q : ℚ) (q0 : 0 ≤ q) (q1 : q ≤ 1)

/-- **The trembled label**: `tremble (procQ q) ε` crosses with weight `(1−ε)·q + ε/2` — derived
from `dp-calibration`'s `tremble_w` (`(1−ε)C(d)(a) + ε·|A_d|⁻¹`), not transcribed: the `/2` is the
uniform tremble over two acts.
Source: [[decision-problems-v2]] §3.1 Definition 10; [[dp-learner-nr-mandate]] target 2 trap
("derive the closed form from the definition, do not transcribe the note's `ε/2`")
Kind: L -/
theorem tremble_procQ_w :
    (tremble (procQ q q0 q1) ε e0 e1 ()).w Act2.a = (1 - ε) * q + ε / 2 := by
  rw [tremble_w]
  have hc : ((Fintype.card Act2 : ℕ) : ℚ) = 2 := by rw [card_act2]; norm_num
  rw [hc]; simp [procQ]; ring

/-- The trembled stay weight. Source: none: infrastructure. Kind: L -/
theorem tremble_procQ_w_b :
    (tremble (procQ q q0 q1) ε e0 e1 ()).w Act2.b = (1 - ε) * (1 - q) + ε / 2 := by
  rw [tremble_w]
  have hc : ((Fintype.card Act2 : ℕ) : ℚ) = 2 := by rw [card_act2]; norm_num
  rw [hc]; simp [procQ]; ring

/-- `P(bot ∣ cross-event)` under a procedure `C` on the bypass tree: `θ/(θ + (1−θ)·C(d)(cross))`.
Source: none: infrastructure
Kind: L -/
theorem tb_pBot (C : Proc Unit (fun _ => Act2) ℚ) :
    nuCond C (tbTheta θ h0 h1) (cell exoBot true) (DpCausalConsist.tbActEv () Act2.a)
      = θ / (θ + (1 - θ) * (C ()).w Act2.a) := by
  unfold nuCond
  rw [tbTheta_nu, tbTheta_nu]
  simp [cell, exoBot, DpCausalConsist.tbActEv, Act2.sum_univ]

/-- **`P(bot ∣ cross-event) = θ/(θ + (1−θ)((1−ε)q + ε/2))`** under the trembled label on the bypass
tree, for every label `q` and tremble `ε`.
Source: [[clean-source-and-policy-responsiveness]] l. 84 ("`P(bad ∣ cross) = θ/(θ + (1−θ)ε/2)`"
at the stay label); [[tb-theta-shadow]]; [[dp-core-2-inventory]] 016; [[dp-learner-nr-mandate]] target 2
Kind: L (two rewrites: `tb_pBot`, the `ν` computation, and `tremble_procQ_w`, the derivation of
`w = (1−ε)q + ε/2` from `tremble_w` — the content is in those; relabelled from P at audit r2)
Fidelity: exact
Hyps: (a) none -/
theorem tb_tremble_pBot :
    nuCond (tremble (procQ q q0 q1) ε e0 e1) (tbTheta θ h0 h1) (cell exoBot true)
        (DpCausalConsist.tbActEv () Act2.a)
      = θ / (θ + (1 - θ) * ((1 - ε) * q + ε / 2)) := by
  rw [tb_pBot, tremble_procQ_w]

/-- **At the stay label**: `P(bot ∣ cross) = θ/(θ + (1−θ)ε/2)` (load-bearing 3).
Source: [[clean-source-and-policy-responsiveness]] l. 84; [[dp-core-2-inventory]] 016;
[[dp-sl-inventory]] 060; [[dp-learner-nr-mandate]] target 2, load-bearing 3
Kind: L (`tb_tremble_pBot` at `q = 0`; relabelled from P at audit r2)
Fidelity: exact
Hyps: (a) none -/
theorem tb_tremble_stay_pBot :
    nuCond (tremble (procQ 0 le_rfl zero_le_one) ε e0 e1) (tbTheta θ h0 h1) (cell exoBot true)
        (DpCausalConsist.tbActEv () Act2.a)
      = θ / (θ + (1 - θ) * (ε / 2)) := by
  rw [tb_tremble_pBot]; ring_nf

/-- **At the cross label**: `P(bot ∣ cross) = θ/(θ + (1−θ)(1 − ε/2))`.
Source: [[tb-theta-shadow]] ("at the cross label it is `0.0525 → 0.05`"); [[dp-learner-nr-mandate]] target 2
Kind: L (`tb_tremble_pBot` at `q = 1`; relabelled from P at audit r2)
Fidelity: exact
Hyps: (a) none -/
theorem tb_tremble_cross_pBot :
    nuCond (tremble (procQ 1 zero_le_one le_rfl) ε e0 e1) (tbTheta θ h0 h1) (cell exoBot true)
        (DpCausalConsist.tbActEv () Act2.a)
      = θ / (θ + (1 - θ) * (1 - ε / 2)) := by
  rw [tb_tremble_pBot]; ring_nf

/-- The act-conditional value of crossing under any `C` on the bypass tree is
`10 − 20·P(bot ∣ cross)` whenever the crossing event has positive mass.
Source: [[dp-learner-nr-mandate]] target 2 ("the evidential value of crossing `= 10 − 20·P(bot ∣ cross)`")
Kind: L -/
theorem tb_condExp_eq_pBot (C : Proc Unit (fun _ => Act2) ℚ)
    (hpos : 0 < θ + (1 - θ) * (C ()).w Act2.a) :
    condExp C (tbTheta θ h0 h1) (DpCausalConsist.tbActEv () Act2.a)
      = 10 - 20 * nuCond C (tbTheta θ h0 h1) (cell exoBot true) (DpCausalConsist.tbActEv () Act2.a) := by
  rw [tb_pBot]
  unfold condExp
  rw [tbTheta_paySum, tbTheta_nu]
  simp [DpCausalConsist.tbActEv, tbPay]
  have hD : θ + (1 - θ) * (C ()).w Act2.a ≠ 0 := hpos.ne'
  have hnum : -(θ * 10) + (1 - θ) * ((C ()).w Act2.a * 10)
      = 10 * (θ + (1 - θ) * (C ()).w Act2.a) - 20 * θ := by ring
  rw [hnum, sub_div, mul_div_assoc, div_self hD, mul_one, mul_div_assoc]

/-- **The evidential value of crossing under the trembled label** on the bypass tree:
`(−10θ + 10(1−θ)w)/(θ + (1−θ)w)` with `w = (1−ε)q + ε/2`, equal to `10 − 20·P(bot ∣ cross)`
(`0 < θ`).
Source: [[dp-core-2-inventory]] 016 ("EDT's value of crossing `−0.26, −8.27, −9.81, −10.00`");
[[dp-learner-nr-mandate]] target 2
Kind: P
Fidelity: exact
Hyps: (a) `0 < θ` (the division guard) -/
theorem tb_tremble_value (hθ0 : 0 < θ) :
    condExp (tremble (procQ q q0 q1) ε e0 e1) (tbTheta θ h0 h1) (DpCausalConsist.tbActEv () Act2.a)
      = (-10 * θ + 10 * (1 - θ) * ((1 - ε) * q + ε / 2)) / (θ + (1 - θ) * ((1 - ε) * q + ε / 2)) ∧
    condExp (tremble (procQ q q0 q1) ε e0 e1) (tbTheta θ h0 h1) (DpCausalConsist.tbActEv () Act2.a)
      = 10 - 20 * (θ / (θ + (1 - θ) * ((1 - ε) * q + ε / 2))) := by
  have hw : 0 ≤ (1 - ε) * q + ε / 2 := by nlinarith
  have hpos : 0 < θ + (1 - θ) * ((1 - ε) * q + ε / 2) := by nlinarith
  have hpos' : 0 < θ + (1 - θ) * (tremble (procQ q q0 q1) ε e0 e1 ()).w Act2.a := by
    rw [tremble_procQ_w]; exact hpos
  have hv := tb_condExp_eq_pBot θ h0 h1 _ hpos'
  rw [tb_tremble_pBot] at hv
  refine ⟨?_, hv⟩
  have hD : θ + (1 - θ) * ((1 - ε) * q + ε / 2) ≠ 0 := hpos.ne'
  have hnum : -10 * θ + 10 * (1 - θ) * ((1 - ε) * q + ε / 2)
      = 10 * (θ + (1 - θ) * ((1 - ε) * q + ε / 2)) - 20 * θ := by ring
  rw [hv, hnum, sub_div, mul_div_assoc, div_self hD, mul_one, mul_div_assoc]

/-- **Swamping at the stay label, explicitly**: for every `δ > 0`, for every tremble
`0 < ε < δθ`, `P(bot ∣ cross) > 1 − δ` and the value of crossing is `< −10 + 20δ`. (The
`Filter.Tendsto` form over `ε → 0⁺`, in ε-δ words: the conditional tends to `1` and the value
to `−10`.)
Source: [[tb-theta-shadow]] ("At the stay label every tremble device is swamped by the fixed
forced mass"; "`0.513, 0.913, 0.991, 1.000` for `ε = 0.1, 0.01, 0.001, 10⁻⁶`");
[[dp-core-2-inventory]] 016; [[dp-learner-nr-mandate]] target 2, load-bearing 3
Kind: P
Fidelity: exact (ε-δ form of the limit; the printed decimals are not theorems)
Hyps: (a) `0 < θ ≤ 1` -/
theorem tb_tremble_stay_swamped (hθ0 : 0 < θ) (δ : ℚ) (hδ : 0 < δ)
    (hε : 0 < ε) (hεδ : ε < δ * θ) :
    1 - δ < nuCond (tremble (procQ 0 le_rfl zero_le_one) ε e0 e1) (tbTheta θ h0 h1)
        (cell exoBot true) (DpCausalConsist.tbActEv () Act2.a) ∧
    condExp (tremble (procQ 0 le_rfl zero_le_one) ε e0 e1) (tbTheta θ h0 h1)
        (DpCausalConsist.tbActEv () Act2.a) < -10 + 20 * δ := by
  have hpos : 0 < θ + (1 - θ) * (ε / 2) := by nlinarith
  have hkey : 1 - δ < θ / (θ + (1 - θ) * (ε / 2)) := by
    rw [lt_div_iff₀ hpos]
    rcases le_or_gt δ 1 with hδ1 | hδ1
    · nlinarith
    · nlinarith
  constructor
  · rw [tb_tremble_stay_pBot]; exact hkey
  · have hv := (tb_tremble_value θ h0 h1 ε e0 e1 0 le_rfl zero_le_one hθ0).2
    rw [hv]
    have : θ / (θ + (1 - θ) * ((1 - ε) * 0 + ε / 2)) = θ / (θ + (1 - θ) * (ε / 2)) := by ring_nf
    rw [this]
    linarith

/-- **dp-sl-2-071's `tremble_neg`, re-founded over `tbTheta`**: at the stay label the value of
crossing is negative for every tremble `0 < ε < 2θ/(1−θ)` (`0 < θ < 1`).
Source: [[dp-sl-2-inventory]] 071 (`tremble_neg`); [[dp-learner-nr-mandate]] target 2
Kind: P
Fidelity: exact
Hyps: (a) `0 < θ < 1`, `0 < ε < 2θ/(1−θ)` -/
theorem tb_tremble_stay_neg (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε)
    (hεθ : ε < 2 * θ / (1 - θ)) :
    condExp (tremble (procQ 0 le_rfl zero_le_one) ε e0 e1) (tbTheta θ h0 h1)
        (DpCausalConsist.tbActEv () Act2.a) < 0 := by
  rw [(tb_tremble_value θ h0 h1 ε e0 e1 0 le_rfl zero_le_one hθ0).1]
  have h1' : 0 < 1 - θ := by linarith
  have hεθ' : ε * (1 - θ) < 2 * θ := by
    rwa [lt_div_iff₀ h1'] at hεθ
  have hpos : 0 < θ + (1 - θ) * ((1 - ε) * 0 + ε / 2) := by nlinarith
  rw [div_neg_iff]
  right
  constructor
  · nlinarith
  · exact hpos

/-- **The deviation gap is `ε`-free**: under the trembled label the all-instance deviation
`V(C[d ↦ cross]) − V(C[d ↦ stay]) = 10(1−θ)` on the bypass tree — `dp-causal-consist`'s
`tb_dev_gap` at `C := tremble (procQ q) ε`, cited.
Source: [[tb-theta-shadow]] ("while the deviation counterfactual is untouched");
[[dp-learner-nr-mandate]] target 2 ("cite, do not re-prove")
Kind: L -/
theorem tb_tremble_dev_gap :
    value ((tremble (procQ q q0 q1) ε e0 e1).deviatePure () Act2.a) (tbTheta θ h0 h1)
      - value ((tremble (procQ q q0 q1) ε e0 e1).deviatePure () Act2.b) (tbTheta θ h0 h1)
      = 10 * (1 - θ) :=
  tb_dev_gap θ h0 h1 _

/-- **The P11 numerals as regression checks**, instances of `tb_condExp_cross`/`tb_stay_condExp`:
`VsCross_zero = −10`; `VsCross_one = 10(1−2θ)`; `cross_positive_iff` (`VsCross_one > 0 ↔ θ < ½`);
`qstar_lt_one_iff` (the tie label `θ/(1−θ) < 1 ↔ θ < ½`, and the value is `0` there); the tie
`VsCross (1/10) (1/9) = 0`.
Source: `sl-workflow/notes/lean/P11-troll-tree-identities.lean` (numerals only); [[dp-sl-inventory]]
060; [[dp-sl-2-inventory]] 071; [[dp-learner-nr-mandate]] target 2
Kind: L
Fidelity: exact (instances)
Hyps: (a) `0 < θ < 1` where a division guard needs it -/
theorem p11_regression (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    condExp (procQ 0 le_rfl zero_le_one) (tbTheta θ h0 h1) (DpCausalConsist.tbActEv () Act2.a) = -10 ∧
    condExp (procQ 1 zero_le_one le_rfl) (tbTheta θ h0 h1) (DpCausalConsist.tbActEv () Act2.a)
      = 10 * (1 - 2 * θ) ∧
    (0 < condExp (procQ 1 zero_le_one le_rfl) (tbTheta θ h0 h1) (DpCausalConsist.tbActEv () Act2.a)
      ↔ θ < 1 / 2) ∧
    (θ / (1 - θ) < 1 ↔ θ < 1 / 2) ∧
    (∀ (hq0 : 0 ≤ θ / (1 - θ)) (hq1 : θ / (1 - θ) ≤ 1),
      condExp (procQ (θ / (1 - θ)) hq0 hq1) (tbTheta θ h0 h1) (DpCausalConsist.tbActEv () Act2.a) = 0) ∧
    condExp (procQ (1/9) (by norm_num) (by norm_num)) (tbTheta (1/10) (by norm_num) (by norm_num))
      (DpCausalConsist.tbActEv () Act2.a) = 0 := by
  have h1' : (1 - θ) ≠ 0 := by linarith
  have h1p : 0 < 1 - θ := by linarith
  have hone : condExp (procQ 1 zero_le_one le_rfl) (tbTheta θ h0 h1) (DpCausalConsist.tbActEv () Act2.a)
      = 10 * (1 - 2 * θ) := by
    rw [tb_condExp_cross]
    have : θ + (1 - θ) * 1 = 1 := by ring
    rw [this, div_one]; ring
  refine ⟨tb_stay_condExp θ h0 h1 hθ0, hone, ?_, ?_, ?_, ?_⟩
  · rw [hone]; constructor <;> intro h <;> linarith
  · rw [div_lt_one h1p]; constructor <;> intro h <;> linarith
  · intro hq0 hq1
    rw [tb_condExp_cross]
    have hnum : -10 * θ + 10 * (1 - θ) * (θ / (1 - θ)) = 0 := by field_simp; ring
    rw [hnum, zero_div]
  · rw [tb_condExp_cross]; norm_num

/-- **N+ for the swamping closed form**: `θ = 1/20`, `ε = 1/10` at the stay label gives
`P(bot ∣ cross) = 20/39`.
Source: [[dp-learner-nr-mandate]] target 2 ("one exact instance (`θ = 1/20, ε = 1/10 ↦ 20/39`)")
Kind: N+ -/
theorem tb_tremble_stay_instance :
    nuCond (tremble (procQ 0 le_rfl zero_le_one) (1/10) (by norm_num) (by norm_num))
        (tbTheta (1/20) (by norm_num) (by norm_num)) (cell exoBot true)
        (DpCausalConsist.tbActEv () Act2.a) = 20 / 39 := by
  rw [tb_tremble_stay_pBot]; norm_num

/-- **`tb_tremble_stay_neg`'s bound is the exact tie**: at `ε = 2θ/(1−θ)` — an admissible tremble
iff `θ ≤ 1/3`, the second conjunct — the stay-label value of crossing on the bypass tree is exactly
`0`: `p11_regression`'s tie label `θ/(1−θ)` read through the tremble (`ε/2 = θ/(1−θ)`). So the
re-founded `tremble_neg` is the exact threshold, not a sufficient condition with slack. Adopted
from audit r2's `TrembleNegSharp` probe.
Source: [[dp-sl-2-inventory]] 071 (`tremble_neg`); [[dp-learner-nr-audit-r2-adversarial]] §3 item
4; [[dp-learner-nr-mandate]] target 2
Kind: P
Fidelity: n/a (sharpness check on `tb_tremble_stay_neg`)
Hyps: (a) `0 < θ < 1` -/
theorem tb_tremble_stay_tie (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (0 ≤ 2 * θ / (1 - θ)) ∧ (2 * θ / (1 - θ) ≤ 1 ↔ θ ≤ 1 / 3) ∧
    ∀ (e0 : 0 ≤ 2 * θ / (1 - θ)) (e1 : 2 * θ / (1 - θ) ≤ 1),
      condExp (tremble (procQ 0 le_rfl zero_le_one) (2 * θ / (1 - θ)) e0 e1) (tbTheta θ h0 h1)
        (DpCausalConsist.tbActEv () Act2.a) = 0 := by
  have h1' : 0 < 1 - θ := by linarith
  refine ⟨div_nonneg (by linarith) h1'.le, ?_, ?_⟩
  · rw [div_le_one h1']
    constructor <;> intro h <;> linarith
  · intro e0 e1
    rw [(tb_tremble_value θ h0 h1 _ e0 e1 0 le_rfl zero_le_one hθ0).1]
    have h1'' : (1 - θ) ≠ 0 := h1'.ne'
    have hnum : -10 * θ + 10 * (1 - θ) * ((1 - 2 * θ / (1 - θ)) * 0 + 2 * θ / (1 - θ) / 2) = 0 := by
      field_simp
      ring
    rw [hnum, zero_div]

end bypass

/-! ## The doc-faithful tree: nothing is swamped -/

section doc

variable (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (ε : ℚ) (e0 : 0 ≤ ε) (e1 : ε ≤ 1)
  (q : ℚ) (q0 : 0 ≤ q) (q1 : q ≤ 1)

/-- **`P(bot ∣ cross-event) = θ` on the doc-faithful tree** under every procedure with positive
crossing weight: both branches cross with the same weight, so conditioning on crossing does not
move `bot`.
Source: [[dp-learner-nr-mandate]] target 2 ("on `tbThetaDoc` it is `θ` at every `ε > 0`")
Kind: P
Fidelity: exact
Hyps: (a) `0 < C(d)(cross)` -/
theorem tbThetaDoc_pBot (C : Proc Unit (fun _ => Act2) ℚ) (hC : 0 < (C ()).w Act2.a) :
    nuCond C (tbThetaDoc θ h0 h1) (cell exoBot true) (DpCausalConsist.tbActEv () Act2.a) = θ := by
  unfold nuCond
  rw [tbThetaDoc_nu, tbThetaDoc_nu]
  simp [cell, exoBot, DpCausalConsist.tbActEv]
  have hden : θ * (C ()).w Act2.a + (1 - θ) * (C ()).w Act2.a = (C ()).w Act2.a := by ring
  rw [hden, mul_div_assoc, div_self hC.ne', mul_one]

/-- **The act-conditional value of crossing is `10 − 20θ` on the doc-faithful tree** under every
procedure with positive crossing weight.
Source: [[dp-learner-nr-mandate]] target 2 ("the act-conditional value of crossing `= 10 − 20θ`")
Kind: P
Fidelity: exact
Hyps: (a) `0 < C(d)(cross)` -/
theorem tbThetaDoc_condExp_cross_of_pos (C : Proc Unit (fun _ => Act2) ℚ)
    (hC : 0 < (C ()).w Act2.a) :
    condExp C (tbThetaDoc θ h0 h1) (DpCausalConsist.tbActEv () Act2.a) = 10 - 20 * θ := by
  unfold condExp
  rw [tbThetaDoc_paySum, tbThetaDoc_nu]
  simp [DpCausalConsist.tbActEv]
  have hden : θ * (C ()).w Act2.a + (1 - θ) * (C ()).w Act2.a = (C ()).w Act2.a := by ring
  rw [hden, div_eq_iff hC.ne']
  ring

/-- Every tremble has positive crossing weight (`ε > 0`). Source: none: infrastructure. Kind: L -/
theorem tremble_procQ_w_pos (hε : 0 < ε) : 0 < (tremble (procQ q q0 q1) ε e0 e1 ()).w Act2.a := by
  rw [tremble_procQ_w]; nlinarith

/-- **Under every tremble device the doc-faithful tree returns `P(bot ∣ cross) = θ` and the value
`10 − 20θ`**, at every label — nothing is swamped.
Source: [[dp-learner-nr-mandate]] target 2; finding (the swamping is bypass-specific)
Kind: P
Fidelity: exact
Hyps: (a) `0 < ε` -/
theorem tbThetaDoc_tremble (hε : 0 < ε) :
    nuCond (tremble (procQ q q0 q1) ε e0 e1) (tbThetaDoc θ h0 h1) (cell exoBot true)
        (DpCausalConsist.tbActEv () Act2.a) = θ ∧
    condExp (tremble (procQ q q0 q1) ε e0 e1) (tbThetaDoc θ h0 h1)
        (DpCausalConsist.tbActEv () Act2.a) = 10 - 20 * θ :=
  ⟨tbThetaDoc_pBot θ h0 h1 _ (tremble_procQ_w_pos ε e0 e1 q q0 q1 hε),
    tbThetaDoc_condExp_cross_of_pos θ h0 h1 _ (tremble_procQ_w_pos ε e0 e1 q q0 q1 hε)⟩

/-- **The contrast, one hypothesis package** (load-bearing 3): under the trembled stay label with
`0 < θ < 1`, `0 < ε ≤ 1`, the bypass tree's `P(bot ∣ cross)` is `θ/(θ + (1−θ)ε/2)` (which
exceeds `θ` whenever `ε < 2`) while the doc-faithful tree's is `θ`; the bypass value is
`10 − 20·θ/(θ + (1−θ)ε/2)` while the doc-faithful value is `10 − 20θ`. The swamping of trembles
by fixed forced mass is a fact about the *bypass* tree, not about the bridge.
Source: [[tb-theta-shadow]] ("'The troll punishes exploration' is reproduced, not confirmed:
fixed forced mass swamps vanishing trembles" — bypass-specific, findings);
[[clean-source-and-policy-responsiveness]] l. 84; [[dp-learner-nr-mandate]] target 2, load-bearing 3
Kind: P
Fidelity: exact
Hyps: (a) `0 < θ < 1`, `0 < ε ≤ 1` -/
theorem swamping_contrast (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    nuCond (tremble (procQ 0 le_rfl zero_le_one) ε e0 e1) (tbTheta θ h0 h1) (cell exoBot true)
        (DpCausalConsist.tbActEv () Act2.a) = θ / (θ + (1 - θ) * (ε / 2)) ∧
    θ < θ / (θ + (1 - θ) * (ε / 2)) ∧
    nuCond (tremble (procQ 0 le_rfl zero_le_one) ε e0 e1) (tbThetaDoc θ h0 h1) (cell exoBot true)
        (DpCausalConsist.tbActEv () Act2.a) = θ ∧
    condExp (tremble (procQ 0 le_rfl zero_le_one) ε e0 e1) (tbTheta θ h0 h1)
        (DpCausalConsist.tbActEv () Act2.a) = 10 - 20 * (θ / (θ + (1 - θ) * (ε / 2))) ∧
    condExp (tremble (procQ 0 le_rfl zero_le_one) ε e0 e1) (tbThetaDoc θ h0 h1)
        (DpCausalConsist.tbActEv () Act2.a) = 10 - 20 * θ := by
  have hpos : 0 < θ + (1 - θ) * (ε / 2) := by nlinarith
  have hlt : θ < θ / (θ + (1 - θ) * (ε / 2)) := by
    rw [lt_div_iff₀ hpos]
    have hden1 : θ + (1 - θ) * (ε / 2) < 1 := by nlinarith
    nlinarith
  obtain ⟨hd1, hd2⟩ := tbThetaDoc_tremble θ h0 h1 ε e0 e1 0 le_rfl zero_le_one hε
  refine ⟨tb_tremble_stay_pBot θ h0 h1 ε e0 e1, hlt, hd1, ?_, hd2⟩
  have hv := (tb_tremble_value θ h0 h1 ε e0 e1 0 le_rfl zero_le_one hθ0).2
  rw [hv]
  have : θ / (θ + (1 - θ) * ((1 - ε) * 0 + ε / 2)) = θ / (θ + (1 - θ) * (ε / 2)) := by ring_nf
  rw [this]

end doc

end Cleanroom.Decision.DpLearnerNr
