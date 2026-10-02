import Cleanroom.Decision.DpLearnerNr.TbThetaDoc

/-!
# `dp-learner-nr` target 4(a), the stay-label caveat made precise

The structural identity `cfMarginal_eq_kPart_general` ("D2 fed the state's cells *is* the
K-partition value") carries the hypothesis `hpos`: every positive cell meets `A` positively. This
file shows the hypothesis is load-bearing — the identity **fails** at the bypass tree's stay label
`q = 0` (`0 < θ < 1`): there the `¬bot` cell has mass `1 − θ > 0` but meets `cross` with mass `0`,
D2 fed the state's cells is `−10θ` (the `¬bot` conditional is the junk `0/0 = 0`), while the
K-partition value is `−10` (the `¬bot` component falls back to Jeffrey on the whole cell, whose
`pr cross = 0`, so only the `bot` cell contributes). So the identity is genuinely a mixed-label
statement, and `cfMarginal_eq_kPart_tb`'s `0 < q` is not decoration. Adopted from audit r2's
`KPartStayLabel` probe (adversarial §3 item 2); the earlier caveat cited `dp-causal-consist`'s
`cfNR_ne_kPart`, which is about `NRAt`'s `cf` — a different object — and is kept for what it is
(findings F4).
-/

namespace Cleanroom.Decision.DpLearnerNr

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Found.DpCoreTree.Catalogue
  Cleanroom.Decision.DpCalibration Cleanroom.Decision.DpCausalConsist Finset

variable (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1)

/-- At the stay label, D2 fed the bypass state's cells is `−10θ`: the `¬bot` cell's conditional
`V_s(cross ∧ ¬bot)` is the junk `0/0 = 0`, so only the `bot` cell (`θ · (−10)`) contributes.
Source: none: infrastructure (for `cfMarginal_ne_kPart_stay`)
Kind: L -/
theorem cfMarginal_stay_label (hθ0 : 0 < θ) :
    cfMarginal (cellDistr (tbState θ h0 h1 0 le_rfl zero_le_one) exoBot)
      (stateE (tbState θ h0 h1 0 le_rfl zero_le_one)) Act2.a = -10 * θ := by
  unfold cfMarginal
  rw [Fintype.sum_bool]
  show (tbState θ h0 h1 0 le_rfl zero_le_one).pr (cell exoBot true) * stateE _ Act2.a true
    + (tbState θ h0 h1 0 le_rfl zero_le_one).pr (cell exoBot false) * stateE _ Act2.a false = _
  unfold stateE
  rw [tbState_pr, tbState_pr, tbState_V, tbState_V]
  simp [cell, exoBot, DpCausalConsist.tbActEv]
  have hθ' : θ ≠ 0 := hθ0.ne'
  field_simp

/-- At the stay label, the K-partition value of `cross` on the bypass state is `−10`: the `¬bot`
component falls back to Jeffrey conditioning on the whole cell, whose `pr cross` is `0`, so only the
`bot` component (`pr cross = 1`, `V cross = −10`) contributes.
Source: none: infrastructure (for `cfMarginal_ne_kPart_stay`)
Kind: L -/
theorem kPart_stay_label (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (kPart (tbState θ h0 h1 0 le_rfl zero_le_one) (DpCausalConsist.tbActEv () Act2.a) exoBot).V
      (DpCausalConsist.tbActEv () Act2.a) = -10 := by
  have hs : SuppRegular (tbState θ h0 h1 0 le_rfl zero_le_one) := by
    unfold tbState; exact suppRegular_calibratedState _ _ _ _
  rw [kPart_V_of_suppRegular _ hs, Fintype.sum_bool, Fintype.sum_bool]
  have hcellT : (tbState θ h0 h1 0 le_rfl zero_le_one).pr (cell exoBot true) = θ := by
    rw [tbState_pr]; simp [cell, exoBot]
  have hcellF : (tbState θ h0 h1 0 le_rfl zero_le_one).pr (cell exoBot false) = 1 - θ := by
    rw [tbState_pr]; simp [cell, exoBot]
  have hposT : 0 < (tbState θ h0 h1 0 le_rfl zero_le_one).pr
      (DpCausalConsist.tbActEv () Act2.a ∩ cell exoBot true) := by
    rw [tbState_pr]; simp [cell, exoBot, DpCausalConsist.tbActEv]; exact hθ0
  have hzeroF : (tbState θ h0 h1 0 le_rfl zero_le_one).pr
      (DpCausalConsist.tbActEv () Act2.a ∩ cell exoBot false) = 0 := by
    rw [tbState_pr]; simp [cell, exoBot, DpCausalConsist.tbActEv]
  have hposF : 0 < (tbState θ h0 h1 0 le_rfl zero_le_one).pr (cell exoBot false) := by
    rw [hcellF]; linarith
  -- the `bot` component: Jeffrey on `cross ∧ bot`, `pr cross = 1`, `V cross = −10`
  have hT : (kPartComp (tbState θ h0 h1 0 le_rfl zero_le_one) (DpCausalConsist.tbActEv () Act2.a)
        exoBot true).pr (DpCausalConsist.tbActEv () Act2.a) = 1 ∧
      (kPartComp (tbState θ h0 h1 0 le_rfl zero_le_one) (DpCausalConsist.tbActEv () Act2.a)
        exoBot true).V (DpCausalConsist.tbActEv () Act2.a) = -10 := by
    unfold kPartComp
    rw [dif_pos hposT, jeffreyCond_pr, jeffreyCond_V, inter_inter_self_left, div_self hposT.ne']
    refine ⟨rfl, ?_⟩
    rw [tbState_V]
    simp [cell, exoBot, DpCausalConsist.tbActEv]
    have hθ' : θ ≠ 0 := hθ0.ne'
    field_simp
  -- the `¬bot` component: `cross ∧ ¬bot` is null, so the fallback is Jeffrey on the cell, and its
  -- `pr cross` is `0`
  have hF : (kPartComp (tbState θ h0 h1 0 le_rfl zero_le_one) (DpCausalConsist.tbActEv () Act2.a)
        exoBot false).pr (DpCausalConsist.tbActEv () Act2.a) = 0 := by
    unfold kPartComp
    rw [dif_neg (by rw [hzeroF]; exact lt_irrefl 0), dif_pos hposF, jeffreyCond_pr, hzeroF,
      zero_div]
  rw [hcellT, hcellF, hT.1, hT.2, hF]
  have hθ' : θ ≠ 0 := hθ0.ne'
  simp
  field_simp

/-- **The K-partition identity fails at the stay label** (`0 < θ < 1`): D2 fed the bypass state's
cells is `−10θ` while the K-partition value is `−10`, so `cfMarginal_eq_kPart_general`'s `hpos`
("every positive cell meets `A` positively") is load-bearing and the identity is a mixed-label
statement. A content check on target 4(a), not a claim about the source.
Source: [[dp-learner-nr-audit-r2-adversarial]] §3 item 2 (probe `KPartStayLabel`); [[dp-learner-nr-mandate]] target 4(a)
Kind: P
Fidelity: n/a (a check that the identity's hypothesis is not decoration)
Hyps: (a) `0 < θ < 1` -/
theorem cfMarginal_ne_kPart_stay (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    cfMarginal (cellDistr (tbState θ h0 h1 0 le_rfl zero_le_one) exoBot)
        (stateE (tbState θ h0 h1 0 le_rfl zero_le_one)) Act2.a
      ≠ (kPart (tbState θ h0 h1 0 le_rfl zero_le_one) (DpCausalConsist.tbActEv () Act2.a) exoBot).V
          (DpCausalConsist.tbActEv () Act2.a) := by
  rw [cfMarginal_stay_label θ h0 h1 hθ0, kPart_stay_label θ h0 h1 hθ0 hθ1]
  intro h; linarith

end Cleanroom.Decision.DpLearnerNr
