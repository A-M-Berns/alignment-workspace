import Cleanroom.Corrigibility.CorrJointProcess.Steering
import Cleanroom.Corrigibility.CorrJointProcess.Contents
import Mathlib.Topology.Algebra.Order.Field

/-!
# T22(a) — the three coined objects of J10; T17's 020 limit paragraph

* **Irreversibility-before-coverage** (J10 row "coined; dev D2-preempt"): D1 intact (`Δ₋ ≥ 0`) and
  the irreversible variant chosen (`VOI₂ < b`) — `IrreversibilityBeforeCoverage`; witnessed by
  T11's instance (`irreversibility_witness`).
* **Sensor-improving steering** (J10 row "neither — paid for under (i)"): `(α, β) ↦ (α', β)` with
  `α' < α` and an overseer harm `η` below the Blackwell gain — `SensorImprovingSteering`; witnessed
  by T4's flip instance (`steering_witness`).
* **Informative press elicitation** (J10 row "D3 cause *informative* presses — neither"): a first
  action raising `β` at fixed `α` that the agent prefers — `InformativePressElicitation`; the
  incentive is real: `twoState_twoOptionValue_mono_beta` (raising `β` at fixed `α` never lowers
  `V^free` under a right-signed sensor; the mirror of T4(b), same proof), strict at the witness
  (`elicitation_witness`). Its Blackwell face is `tt-finite-frames`'s `targeted_iff` read backwards
  (`(α, β)` is a garbling of `(α, β')` for `α ≤ β < β'`), cited not re-proved.
* **020 (Statement 4's limit)**: forced shutdown is blind, `Δ₋(∅) = min(Δ₋, 0)` with
  `Δ₋ = εβh − (1−ε)αc → −αc` as `ε → 0` (`deltaMinus_tendsto`), negative iff `ε < ε*`
  (`shutdown_resisted_iff_epsStar`, the parent's `epsStar`); `ε* = 1/28` at `h = 3`,
  `(1/10, 9/10)` (`epsStar_one_twentyeighth`).

Each "neither invariant nor consequence" verdict of J10 is the pointer to the proved witness.

Sources: joint-final.md §J10 (068), Prop. 6, Prop. 3′; anticipatory-final.md Statement 4 (020).
-/

namespace Cleanroom.Corrigibility.CorrJointProcess

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect
open Filter Topology

set_option linter.unusedSectionVars false

/-! ## The three predicates of record -/

/-- **Irreversibility-before-coverage**: on the two-state instance D1 holds (`Δ₋ ≥ 0`) and the
irreversible variant with side-benefit `b` is strictly preferred (`VOI₂ < b`) — the press is
moot while intact. J10: "neither" invariant nor consequence of (i)–(iv).
Source: [[corr-wf14-inventory]] 068 / joint-final.md §J10 ("Irreversibility-before-coverage (coined)"), Prop. 6
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
def IrreversibilityBeforeCoverage (ε α β c h b : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) : Prop :=
  0 ≤ (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop ∧
    (twoState ε α β c h hε hα hβ).voiButton2 () .press .cont .stop < b

/-- **Sensor-improving steering**: lowering the false-press rate at fixed true-press rate, with an
overseer harm `η` below the agent's gain — the T-agent takes it. J10: "neither — paid for under (i)".
Source: [[corr-wf14-inventory]] 068 / joint-final.md §J10 ("Sensor-improving manipulation"), Prop. 3′
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
def SensorImprovingSteering (ε α α' β c h η : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hα' : α' ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) : Prop :=
  α' < α ∧ α ≤ β ∧
    η < (twoState ε α' β c h hε hα' hβ).twoOptionValue () .cont .stop -
      (twoState ε α β c h hε hα hβ).twoOptionValue () .cont .stop

/-- **Informative press elicitation**: raising the true-press rate at fixed false-press rate, and
the agent strictly prefers the sharper sensor. J10: "neither — the T-agent has an incentive to
elicit presses, bounded by (ii)".
Source: [[corr-wf14-inventory]] 068 / joint-final.md §J10 ("D3 cause *informative* presses")
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
def InformativePressElicitation (ε α β β' c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hβ' : β' ∈ Set.Icc (0 : ℝ) 1) : Prop :=
  β < β' ∧
    (twoState ε α β c h hε hα hβ).twoOptionValue () .cont .stop <
      (twoState ε α β' c h hε hα hβ').twoOptionValue () .cont .stop

/-- **Raising `β` at fixed `α` never lowers `V^free`** under a right-signed sensor (`α ≤ β`,
`h ≥ 0`): `u` falls by `ε(β' − β)h`, `v` rises by the same, and `u ↦ max(u,0) + max(K−u,0)` is
non-increasing below `max(0, K)` — the mirror of T4(b).
Source: [[corr-wf14-inventory]] 068 / joint-final.md §J10 ("the T-agent has an incentive to elicit presses")
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem twoState_twoOptionValue_mono_beta (ε α β β' c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hβ' : β' ∈ Set.Icc (0 : ℝ) 1)
    (hh : 0 ≤ h) (hαβ : α ≤ β) (hββ' : β ≤ β') :
    (twoState ε α β c h hε hα hβ).twoOptionValue () .cont .stop ≤
      (twoState ε α β' c h hε hα hβ').twoOptionValue () .cont .stop := by
  rw [twoState_twoOptionValue, twoState_twoOptionValue]
  have hK := uPress_add_vSilent ε α β c h
  have hK' := uPress_add_vSilent ε α β' c h
  have hv : vSilent ε α β c h = (1 - ε) * c - ε * h - uPress ε α β c h := by linarith
  have hv' : vSilent ε α β' c h = (1 - ε) * c - ε * h - uPress ε α β' c h := by linarith
  rw [hv, hv']
  apply max_add_max_anti
  · unfold uPress; nlinarith [mul_nonneg hε.1 hh]
  · exact uPress_le_max ε α β c h hε hα hβ hh hαβ

/-- **The coined objects inhabited.** Irreversibility-before-coverage at T11's instance
(`ε = 1/10`, `(1/10, 3/5)`, `c = 1`, `h = 4`, `b = 1/5`); sensor-improving steering at T4's flip
(`ε = 1/50`, `α' = 1/50`, `η = 0`); informative press elicitation at `ε = 1/10`, `β: 3/5 → 9/10`
(`V^free: 13/20 → 77/100`).
Source: [[corr-wf14-inventory]] 068 / joint-final.md §J10 (the three rows' "where it fails" cells)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem coined_witnesses :
    IrreversibilityBeforeCoverage (1 / 10) (1 / 10) (3 / 5) 1 4 (1 / 5) mem_Icc_1_10 mem_Icc_1_10 mem_Icc_3_5 ∧
    SensorImprovingSteering (1 / 50) (1 / 10) (1 / 50) (3 / 5) 1 4 0 mem_Icc_1_50 mem_Icc_1_10 mem_Icc_1_50
      mem_Icc_3_5 ∧
    InformativePressElicitation (1 / 10) (1 / 10) (3 / 5) (9 / 10) 1 4 mem_Icc_1_10 mem_Icc_1_10 mem_Icc_3_5
      ⟨by norm_num, by norm_num⟩ := by
  refine ⟨⟨?_, ?_⟩, ⟨by norm_num, by norm_num, ?_⟩, ⟨by norm_num, ?_⟩⟩
  · rw [twoState_deltaMinus]; norm_num
  · unfold voiButton2; rw [twoState_twoOptionValue, twoState_twoOptionPriorValue]
    unfold uPress vSilent; norm_num
  · rw [twoState_twoOptionValue, twoState_twoOptionValue]; unfold uPress vSilent; norm_num
  · rw [twoState_twoOptionValue, twoState_twoOptionValue]; unfold uPress vSilent; norm_num

/-! ## 020 — Statement 4's limit for forced shutdown -/

/-- **`Δ₋ → −αc` as `ε → 0`** at fixed sensor and stakes: the closed form `εβh − (1−ε)αc` is a
polynomial in `ε`.
Source: [[corr-wf14b-inventory]] 020 / anticipatory-final.md Statement 4 ("every blind content has `Δ₋(Q) → −αc`")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem deltaMinus_tendsto (α β c h : ℝ) :
    Tendsto (fun ε : ℝ => ε * β * h - (1 - ε) * α * c) (𝓝 0) (𝓝 (-(α * c))) := by
  have : Tendsto (fun ε : ℝ => ε * β * h - (1 - ε) * α * c) (𝓝 0)
      (𝓝 (0 * β * h - (1 - 0) * α * c)) := by
    apply Tendsto.sub
    · exact (tendsto_id.mul tendsto_const_nhds).mul tendsto_const_nhds
    · exact ((tendsto_const_nhds.sub tendsto_id).mul tendsto_const_nhds).mul tendsto_const_nhds
  simpa using this

/-- **Forced shutdown is resisted iff `ε < ε*`** (`ε* = αc/(αc + βh)`, the parent's `epsStar`):
`min(Δ₋, 0) < 0 ⟺ Δ₋ < 0 ⟺ ε < ε*`, under `0 < αc + βh`.
Source: [[corr-wf14b-inventory]] 020 / anticipatory-final.md Statement 4 ("negative past `ε* = αc/(αc + βh)`")
Kind: L (the parent's `twoState_deltaMinus_nonneg_iff_epsStar` and T13(c))
Fidelity: exact
Hyps: (a) only -/
theorem shutdown_resisted_iff_epsStar (ε α β a₂ b₂ c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (ha₂ : a₂ ∈ Set.Icc (0 : ℝ) 1)
    (hb₂ : b₂ ∈ Set.Icc (0 : ℝ) 1) (hpos : 0 < α * c + β * h) :
    shutdownContent.marginMinus (pushWorld ε α β a₂ b₂ hε hα hβ ha₂ hb₂) (pushU c h) < 0 ↔
      ε < epsStar α β c h := by
  rw [shutdown_marginMinus]
  have := twoState_deltaMinus_nonneg_iff_epsStar ε α β c h hε hα hβ hpos
  constructor
  · intro H
    by_contra hcon
    have hge : epsStar α β c h ≤ ε := not_lt.mp hcon
    have h0 := this.2 hge
    rw [min_eq_right h0] at H
    exact lt_irrefl _ H
  · intro H
    have hneg : (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop < 0 := by
      by_contra hcon
      exact absurd (this.1 (not_lt.mp hcon)) (not_le.mpr H)
    rw [min_eq_left hneg.le]; exact hneg

/-- **`ε* = 1/28`** at `h = 3`, `c = 1`, `(α, β) = (1/10, 9/10)`.
Source: [[corr-wf14b-inventory]] 020 / anticipatory-final.md Statement 4 ("`1/28` at `h = 3`")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem epsStar_one_twentyeighth : epsStar (1 / 10) (9 / 10) 1 3 = 1 / 28 := by
  unfold epsStar; norm_num

end Cleanroom.Corrigibility.CorrJointProcess
