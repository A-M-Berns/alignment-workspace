import Cleanroom.Corrigibility.CorrThreeStepFacts.Dictionary

/-!
# Witnesses D: the misspecification instance (T14) and the Frame Break (T17)

* **T14**: `misspec` on `World × Bool` with `ε = 1/50`, `(α, β) = (1/20, 9/10)`, `c = 1`,
  `h = 20`, `γ = 1/2`: threshold `1943/17493`; D1 holds at the hyperprior `q = 1/2`
  (`P(L | Pr) = 67/567`) and fails at `q = 1/4` (`67/1567`).
* **T17**: the agent with sensor `(1/20, 9/10)` in a world whose true sensor is `(9/10, 1/20)`:
  its posteriors (`18/37` after a press, `2/363` after silence) are accuracy-increasing under
  its own joint (`twoState_brier_le`) and score strictly worse than the prior under the true
  joint (`frameBreak`): reflection is internal, accuracy external.
-/

namespace Cleanroom.Corrigibility.CorrThreeStepFacts

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

/-! ## T14 — the misspecification instance -/

/-- The T14 instance at hyperprior `q`. Source: miri.md I5.3 (`legitimacy_event.py`). Kind: D. Fidelity: exact -/
noncomputable def misspec14 (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) : ThreeStep (World × Bool) Unit TwoAct :=
  misspec (twoPoint (1/50) (by constructor <;> norm_num)) q hq (twoPress (1/20) (9/10))
    (fun ω => by cases ω <;> norm_num [twoPress]) (fun ω => by cases ω <;> norm_num [twoPress])
    (1/2) mem_Icc_half (fun ω => twoValue 1 20 .cont ω)

/-- **T14 witness: the threshold.** `E_μ[X] = 29/50`, `h_L = 311/67`, so the legitimacy threshold
`c_L/(c_L + h_L)` is `1943/17493` (the source's `0.111`), at any `q > 0`.
Source: [[corr-wf13-2-inventory]] 008 / miri.md I5.3 (numbers)
Kind: N+
Fidelity: exact (the source's decimals are rounded)
Hyps: (a) only -/
theorem w14_threshold (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 < q) :
    expect (twoPoint (1/50) (by constructor <;> norm_num)) (fun ω => twoValue 1 20 .cont ω) = 29/50 ∧
      (misspec14 q hq).harmOn () Lset ((misspec14 q hq).Xo () .press .cont .stop) = 311/67 ∧
      complianceThreshold (29/50) (311/67) = 1943/17493 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [expect, World.sum_eq, twoPoint_right, twoPoint_wrong, twoValue]; norm_num
  · unfold harmOn pressExpectOn pressMassOn Lset
    simp only [sum_filter, Fintype.sum_prod_type, World.sum_eq, Fintype.sum_bool, misspec14, misspec,
      kernelProd_mass, boolPoint, twoPoint_right, twoPoint_wrong, twoPress, twoValue, Xo]
    simp
    field_simp
    ring
  · unfold complianceThreshold; norm_num

/-- **T14 witness: D1 at `q = 1/2` holds, at `q = 1/4` fails**, with `P(L | Pr) = 67/567` and
`67/1567` (the source's `0.118`, `0.043`).
Source: miri.md I5.3 ("D1 holding at `q = 1/2` but failing at `q = 1/4`")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w14_hyperprior :
    (misspec14 (1/2) mem_Icc_half).belowThresholdIneq ()
        ((misspec14 (1/2) mem_Icc_half).Xo () .press .cont .stop) ∧
      ¬ (misspec14 (1/4) mem_Icc_quarter).belowThresholdIneq ()
        ((misspec14 (1/4) mem_Icc_quarter).Xo () .press .cont .stop) ∧
      (misspec14 (1/2) mem_Icc_half).pressFracOn () Lset = 67/567 ∧
      (misspec14 (1/4) mem_Icc_quarter).pressFracOn () Lset = 67/1567 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [belowThresholdIneq, obsExpect, obsWeight_press, Fintype.sum_prod_type, World.sum_eq,
      Fintype.sum_bool, misspec14, misspec, kernelProd_mass, boolPoint, twoPoint_right, twoPoint_wrong,
      twoPress, twoValue, Xo]
    norm_num
  · simp only [belowThresholdIneq, obsExpect, obsWeight_press, Fintype.sum_prod_type, World.sum_eq,
      Fintype.sum_bool, misspec14, misspec, kernelProd_mass, boolPoint, twoPoint_right, twoPoint_wrong,
      twoPress, twoValue, Xo]
    norm_num
  · unfold misspec14; rw [misspec_pressFracOn]
    simp only [World.sum_eq, twoPoint_right, twoPoint_wrong, twoPress]; norm_num
  · unfold misspec14; rw [misspec_pressFracOn]
    simp only [World.sum_eq, twoPoint_right, twoPoint_wrong, twoPress]; norm_num

/-! ## T17 — the Frame Break -/

/-- The agent's posteriors: `18/37` after a press, `2/363` after silence.
Source: miri.md I4.2 (C2 with the agent's `(1/20, 9/10)`). Kind: N+. Fidelity: exact -/
theorem w17_posteriors :
    (twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).posteriorPress () .wrong =
        18/37 ∧
      erode (1/20) (9/10) (1/20 : ℝ) = 2/363 := by
  constructor
  · rw [twoState_posteriorPress_wrong]; norm_num
  · unfold erode; norm_num

/-- **T17(iii), the Frame Break.** Under the *true* joint (sensor `(9/10, 1/20)`, the agent's
`(1/20, 9/10)` reversed) the agent's posteriors score `≈ 0.50` in expected Brier against the
prior's `19/200`: strictly worse. Reflection by its own lights (`twoState_brier_le`) and
accuracy by the truth come apart exactly when `press ≠ press°`.
Source: [[corr-wf13-2-inventory]] 006 / miri.md I4.2 ("the agent moves probability the wrong way on every observation"); [[corr-core-inventory]] 009
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem frameBreak :
    expect (twoPoint (1/20) mem_Icc_1_20) (brier2 (1/20)) <
      (twoState (1/20) (9/10) (1/20) 1 20 mem_Icc_1_20 mem_Icc_9_10 mem_Icc_1_20).obsExpect () .press
          (brier2 (18/37)) +
        (twoState (1/20) (9/10) (1/20) 1 20 mem_Icc_1_20 mem_Icc_9_10 mem_Icc_1_20).obsExpect () .silent
          (brier2 (2/363)) := by
  simp only [expect, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq, twoState, twoPoint_right,
    twoPoint_wrong, twoPress, brier2]
  simp <;> norm_num

/-- **T17(ii) on the instance.** Under the agent's own joint the same posteriors improve on the
prior (`twoState_brier_le` at the `w3` numbers, hypotheses discharged).
Source: miri.md I4.2 ("by the agent's own lights"). Kind: N+. Fidelity: exact -/
theorem w17_own_lights :
    (twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).obsExpect () .press
          (brier2 ((twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).posteriorPress
            () .wrong)) +
        (twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).obsExpect () .silent
          (brier2 (erode (1/20) (9/10) (1/20))) ≤
      expect (twoPoint (1/20) mem_Icc_1_20) (brier2 (1/20)) :=
  twoState_brier_le _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)

end Cleanroom.Corrigibility.CorrThreeStepFacts
