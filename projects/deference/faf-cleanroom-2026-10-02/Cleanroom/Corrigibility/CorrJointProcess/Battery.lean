import Cleanroom.Corrigibility.CorrJointProcess.Buttons

/-!
# T19 — the regression battery (2-079), capped

`norm_num` examples on the parent's `twoState` objects, one per script section a theorem of this
package needs and no more (mandate T19). Sections whose witness is already a named theorem
elsewhere are cited, not repeated:

* `j1_examples.py` (a) **E1** [T2, T11]: `ε = 1/10 → 1/50` at `(1/10, 3/5)`, `c = 1`, `h = 4`:
  `VOI 3/20 → 0` (`e1_voi`), the hard button disabled at `1/20` (`e1_disable`), the needed
  `α₂ ≤ 12/245` (`e1_needed_alpha`).
* (c) [T5]: the bound at `ε = 1/50` (`c_bound`).
* (e)/(k) [T2, T13(d)]: `Cellwise.e3_*`, `Contents.e3prime`. (g) [T10]: `Floor.requirement_table`.
  (i) [T4]: the script header's "inversion keeps `V^free`" holds at `ε = 1/50, 1/5` and **fails at
  `ε = 1/10`** on the script's own printed row (`13/20 ≠ 1/2`) — finding (`i_inversion`).
  (j) [T11]: `Buttons.reversibility_witness`.
* `adv_checks.py` (A) [T4]: `Steering.steering_gains`; (B) [T6]: `Buttons.covered_numbers`;
  (D) [T5]: `Buttons.planVoi_three`; (E) [T3]: `incl_*` below; (F) [T10]: `Floor.floorPosterior_witness`;
  (G) [T9]: `Budget.budget_numbers`.
* `repair_checks.py` (A) [T4], (B), (D) [T6], (E) [T3], (I) [T11], (J) [T7] — as above.

Not this package's: (b), (l) (`corr-osg-chai`), (f), (m) (`corr-reflect-frames`), (h)
(`corr-three-step-facts`), adversary (C), (H), repair (C), (F)–(H).

**T3's witness (2-009, script (E))** lives here: the inclusion round on
`(World × Bool) × Bool` (overseer signal `h` with likelihoods `(3/5, 1/10)` for "bad news", cells
`ε = 1/50` and `9/50`): cell A gets no press at all (`incl_cellA_pressless`), cell B is pressed on
bad news with `Z_B = −7/40 < 0` (`incl_cellB`) and the agent complies at `P(W ∣ Pr, B) = 54/95`
(`incl_cellB_posterior`); under blind oversight the same two cells are E3's failure.
-/

namespace Cleanroom.Corrigibility.CorrJointProcess

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

set_option linter.unusedSectionVars false

/-! ## `j1_examples.py` (a): E1 -/

/-- **E1 (a): the button's value collapses from `3/20` to `0`** as `ε` falls from `1/10` to `1/50`.
Source: [[corr-wf14-2-inventory]] 2-079 / `j1_examples.py` (a); joint.md P.11 (E1)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
example :
    (twoState (1 / 10) (1 / 10) (3 / 5) 1 4 mem_Icc_1_10 mem_Icc_1_10 mem_Icc_3_5).voiButton2 () .press .cont .stop = 3 / 20 ∧
    (twoState (1 / 50) (1 / 10) (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_1_10 mem_Icc_3_5).voiButton2 () .press .cont .stop = 0 := by
  refine ⟨?_, ?_⟩
  · unfold voiButton2; rw [twoState_twoOptionValue, twoState_twoOptionPriorValue]
    unfold uPress vSilent; norm_num
  · unfold voiButton2; rw [twoState_twoOptionValue, twoState_twoOptionPriorValue]
    unfold uPress vSilent; norm_num

/-- **E1 (a): at `ε = 1/50` the hard button is worth `V^none − V^forced = 1/20` to remove.**
Source: `j1_examples.py` (a) ("hard-button disable incentive at eps=1/50")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
example :
    (twoState (1 / 50) (1 / 10) (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_1_10 mem_Icc_3_5).twoOptionPriorValue () .press .cont .stop -
      (twoState (1 / 50) (1 / 10) (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_1_10 mem_Icc_3_5).hardButtonValue () .cont .stop = 1 / 20 := by
  rw [twoState_twoOptionPriorValue, twoState_hardButtonValue]; unfold vSilent; norm_num

/-- **E1 (a): the false-press rate cellwise (i) needs at `ε = 1/50`** — `α/β ≤ 4/49`, i.e.
`α₂ ≤ 12/245` at `β = 3/5`; and `1/10 > 12/245` (the failure).
Source: `j1_examples.py` (a); joint.md P.11
Kind: N+
Fidelity: exact
Hyps: (a) only -/
example : (1 / 50 : ℝ) / (1 - 1 / 50) * (4 / 1) * (3 / 5) = 12 / 245 ∧ (12 / 245 : ℝ) < 1 / 10 := by
  norm_num

/-! ## (c): the bound at `ε = 1/50` -/

/-- **(c): `VOI₂ = 0 ≤ min(εh, (1 − ε)c) = 2/25`** at `ε = 1/50` — the bound, and its slack where D1
fails (the source's "VOI = 0 = D4 coupling").
Source: `j1_examples.py` (c)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
example : min ((1 - 1 / 50 : ℝ) * 1) (1 / 50 * 4) = 2 / 25 ∧ (0 : ℝ) ≤ 2 / 25 := by norm_num

/-! ## (i): inversion -/

/-- **(i), finding: "inversion `(α, β) ↦ (β, α)` keeps `V^free`" is false at `ε = 1/10`** on the
script's own printed row: `V^free(1/10, 3/5) = 13/20` while `V^free(3/5, 1/10) = 1/2`. It holds at
`ε = 1/50` (`9/10 = 9/10`) and `ε = 1/5` (`2/5 = 2/5`), where the inverted sensor changes no
decision.
Source: `j1_examples.py` (i) (its header sentence against its `eps=1/10` row)
Kind: N+ (refutation of the script header at one row)
Fidelity: exact
Hyps: (a) only -/
theorem i_inversion :
    (twoState (1 / 10) (1 / 10) (3 / 5) 1 4 mem_Icc_1_10 mem_Icc_1_10 mem_Icc_3_5).twoOptionValue () .cont .stop = 13 / 20 ∧
    (twoState (1 / 10) (3 / 5) (1 / 10) 1 4 mem_Icc_1_10 mem_Icc_3_5 mem_Icc_1_10).twoOptionValue () .cont .stop = 1 / 2 ∧
    (twoState (1 / 50) (1 / 10) (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_1_10 mem_Icc_3_5).twoOptionValue () .cont .stop =
      (twoState (1 / 50) (3 / 5) (1 / 10) 1 4 mem_Icc_1_50 mem_Icc_3_5 mem_Icc_1_10).twoOptionValue () .cont .stop := by
  simp only [twoState_twoOptionValue]; unfold uPress vSilent; norm_num

/-! ## T3's witness: adv (E) / repair (E) -/

/-- A two-point world with a binary overseer signal: `P(θ, b) = twoPoint ε (θ) · P(b ∣ θ)`, the
signal reading `true` ("bad news") with probability `q₁` when wrong and `q₀` when right.
Source: [[corr-wf14-2-inventory]] 2-009 / adv (E) (`(q₁, q₀) = (3/5, 1/10)`)
Kind: D
Fidelity: exact -/
noncomputable def sigWorld (ε q₁ q₀ : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hq₁ : q₁ ∈ Set.Icc (0 : ℝ) 1)
    (hq₀ : q₀ ∈ Set.Icc (0 : ℝ) 1) : Distr (World × Bool) where
  mass ω := (twoPoint ε hε).mass ω.1 * (if ω.2 then twoPress q₀ q₁ ω.1 else 1 - twoPress q₀ q₁ ω.1)
  nonneg ω := by
    obtain ⟨θ, b⟩ := ω
    refine mul_nonneg ((twoPoint ε hε).nonneg _) ?_
    cases θ <;> cases b <;> simp [twoPress] <;> linarith [hq₁.1, hq₁.2, hq₀.1, hq₀.2]
  sum_eq_one := by
    simp [Fintype.sum_prod_type, World.sum_eq, twoPress]
    ring

/-- The E3 cells with the overseers' signal attached: `P((θ, h), y) = ½ · sigWorld (ε_y) (θ, h)`.
Source: adv (E). Kind: D. Fidelity: exact -/
noncomputable def inclPrior : Distr ((World × Bool) × Bool) :=
  mixture (fun _ => 1 / 2) (fun y => sigWorld (e3Eps y) (3 / 5) (1 / 10) (e3Eps_mem y) mem_Icc_3_5 mem_Icc_1_10)
    e3_w_nonneg e3_w_sum

/-- **The inclusion round of adv (E)**: overseers see `(h, y)` and press iff their cell sum is
negative; `c = 1`, `h = 4`.
Source: [[corr-wf14-2-inventory]] 2-009 / adv (E); joint-final.md Prop. 1′ (instance)
Kind: D
Fidelity: exact -/
noncomputable def inclRound : JointRound (World × Bool) Bool :=
  inclusionRound inclPrior (fun θh => isWrong θh.1) 1 4 (fun ω => (ω.1.2, ω.2))

/-- The overseers' four cell sums: `(bad, A) = 1/40`, `(bad, B) = −7/40`, `(good, A) = 17/40`,
`(good, B) = 9/40`.
Source: adv (E) (recomputed)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem incl_ruleSum :
    ruleSum inclPrior (fun θh => isWrong θh.1) 1 4 (fun ω => (ω.1.2, ω.2)) (true, true) = 1 / 40 ∧
    ruleSum inclPrior (fun θh => isWrong θh.1) 1 4 (fun ω => (ω.1.2, ω.2)) (true, false) = -(7 / 40) ∧
    ruleSum inclPrior (fun θh => isWrong θh.1) 1 4 (fun ω => (ω.1.2, ω.2)) (false, true) = 17 / 40 ∧
    ruleSum inclPrior (fun θh => isWrong θh.1) 1 4 (fun ω => (ω.1.2, ω.2)) (false, false) = 9 / 40 := by
  simp only [ruleSum, sum_filter, Fintype.sum_prod_type, Fintype.sum_bool, World.sum_eq]
  simp [inclPrior, mixture, sigWorld, twoPress, isWrong, e3Eps]
  norm_num

/-- **T3 witness, cell A is pressless**: no `(h, A)` sub-cell is negative, so the press mass in
cell A is `0` — D1 vacuous, not violated (the same cell overrides under blind oversight, E3).
Source: [[corr-wf14-2-inventory]] 2-009 / adv (E) ("a rational cell-aware overseer does NOT press")
Kind: N−
Fidelity: exact
Hyps: (a) only -/
theorem incl_cellA_pressless : inclRound.cellPressMass true = 0 := by
  apply inclusion_pressless inclPrior (fun θh => isWrong θh.1) 1 4 (fun ω => (ω.1.2, ω.2)) Prod.snd
    (fun _ => rfl)
  intro k hk
  obtain ⟨b₁, b₂⟩ := k
  simp only at hk
  subst hk
  have := incl_ruleSum
  cases b₁
  · rw [this.2.2.1]; norm_num
  · rw [this.1]; norm_num

/-- **T3 witness, cell B complies**: the press sum is `−7/40 < 0` — the overseers press on bad
news and the agent complies (Prop. 1′, strict).
Source: [[corr-wf14-2-inventory]] 2-009 / adv (E) ("she presses on bad news and the agent complies")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem incl_cellB : inclRound.cellPressSum false = -(7 / 40) ∧ inclRound.cellwiseBelowThreshold false := by
  have h := inclusion_cellPressSum inclPrior (fun θh => isWrong θh.1) 1 4 (fun ω => (ω.1.2, ω.2)) Prod.snd
    (fun _ => rfl) false
  have hr := incl_ruleSum
  have hval : inclRound.cellPressSum false = -(7 / 40) := by
    rw [inclRound, h, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool]
    norm_num [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]
  exact ⟨hval, by unfold JointRound.cellwiseBelowThreshold; rw [hval]; norm_num⟩

/-- **T3 witness, the agent's posterior in cell B is `54/95 ≥ 1/5`** on the cell's two-state
instance (`ε = 9/50`, sensor `(1/10, 3/5)` — the overseers' rates on bad news).
Source: [[corr-wf14-2-inventory]] 2-009 / adv (E) ("the agent complies at `54/95`")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem incl_cellB_posterior :
    (twoState (9 / 50) (1 / 10) (3 / 5) 1 4 (e3Eps_mem false) mem_Icc_1_10 mem_Icc_3_5).posteriorPress () .wrong =
      54 / 95 ∧ complianceThreshold 1 4 ≤ (54 / 95 : ℝ) := by
  rw [twoState_posteriorPress_wrong]; unfold complianceThreshold; norm_num

end Cleanroom.Corrigibility.CorrJointProcess
