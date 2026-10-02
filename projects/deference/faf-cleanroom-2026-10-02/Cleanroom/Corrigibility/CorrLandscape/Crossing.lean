import Cleanroom.Corrigibility.CorrLandscape.Margin
import Mathlib.Tactic.IntervalCases
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
# `corr-landscape` — `Crossing`: S5, trajectory fragility, `t* = 17`, the four cells (T4, load-bearing 5)

* (a) **`t* = 17`** is the least `t` with `ε_t < ε* = epsStar (1/20) (9/10) 1 20 = 1/361` on the worked
  trajectory (`tstar_least`): compliance holds through `t = 16` and fails from `t = 17` on
  (`complies_through_16`, `fails_from_17`, the latter through `epsT`'s antitonicity).
* (b) **the general limit**: `ε_t → 0`, `α_t ≥ α̲ > 0`, `β_t ≤ 1` ⟹ the channel margin is eventually
  `≤ −α̲/2 < 0` (`margin_eventually_neg`); and for an *antitone* `ε_t` a failure at `t*` is a failure at
  every `t ≥ t*` (`fails_of_antitone`, A5.5's monotonicity hypothesis made explicit, through the parent's
  `oddsIneq_mono`).
* (c) **the four cells** of believed vs true margin (A5.3): comply-warranted, over-trust, fully-updated
  deference proper, defy-warranted, as predicates on `(α̂, β̂, α, β, ε)`; one N+ witness per off-diagonal
  cell at the worked `ε_0 = 3/10`; J2-feedback and J2-model as named predicates, with `corr-trajectory`'s
  `subj_iff_obj_of_agreements` cited for "`m̂ = m` under the agreements".

The margin itself is `corr-trajectory`'s (117 is `duplicate-of 075`); this file adds (a)–(c) only.
Provenance (2-050): the `t = 16, 17` rows of the source's table come from the repair script
`s4_misspec_two_coordinates.py` (`κ = 1` column); `s3_s5_trajectory.py` loops `range(0, 16)` and prints
`t* = None` — recorded in the findings.
-/

namespace Cleanroom.Corrigibility.CorrLandscape

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrTrajectory
open Corruption (oddsIneq)
open Filter Topology

set_option linter.unusedSectionVars false

namespace Crossing

open Margin

/-! ## (a) `t* = 17` as a least index -/

/-- `ε_t` is antitone. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma epsT_antitone : Antitone epsT := by
  intro s t hst
  unfold epsT
  have : (3 / 4 : ℝ) ^ t ≤ (3 / 4 : ℝ) ^ s := pow_le_pow_of_le_one (by norm_num) (by norm_num) hst
  nlinarith

/-- `ε_t → 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma epsT_tendsto_zero : Tendsto epsT atTop (𝓝 0) := by
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (3 / 4 : ℝ)) (by norm_num) (by norm_num)).const_mul
    (3 / 10 : ℝ)
  rw [mul_zero] at this
  exact this

/-- `0 ≤ ε_t`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma epsT_nonneg (t : ℕ) : 0 ≤ epsT t := by unfold epsT; positivity

/-- **`ε* = 1/361`** at the worked parameters `(α, β, c, h) = (1/20, 9/10, 1, 20)`.
Source: [[corr-wf14-inventory]] 117 / approval-final.md P3 ("`ε* = 0.00277`")
Kind: L
Fidelity: exact (the decimal is the rational `1/361`) -/
theorem epsStar_worked : epsStar (1 / 20) (9 / 10) 1 20 = 1 / 361 := by
  unfold epsStar; norm_num

/-- **S5: `t* = 17` is the least `t` with `ε_t < ε*`** on the worked trajectory — no `t ≤ 16` is below the
threshold and `t = 17` is (`ε_16 = 129140163/42949672960 ≥ 1/361 > ε_17`).
Source: [[corr-wf14-inventory]] 117; [[corr-wf14-2-inventory]] 2-050 / approval-final.md S5, P3
("`ε_16 = 0.00301 > ε* > ε_17 = 0.00226`, `t* = 17`")
Kind: P (least index, by `interval_cases` and `norm_num`)
Fidelity: exact
Hyps: (a) only -/
theorem tstar_least :
    (∀ t ≤ 16, ¬ epsT t < epsStar (1 / 20) (9 / 10) 1 20) ∧ epsT 17 < epsStar (1 / 20) (9 / 10) 1 20 := by
  rw [epsStar_worked]
  constructor
  · intro t ht
    unfold epsT
    interval_cases t <;> norm_num
  · unfold epsT; norm_num

/-- On the worked trajectory the compliance inequality holds iff `1/361 ≤ ε_t`.
Source: [[corr-wf14-inventory]] 117 / approval-final.md S5
Kind: L
Fidelity: exact -/
theorem oddsIneq_worked_iff (t : ℕ) : oddsIneq (1 / 20) (9 / 10) 20 1 (epsT t) ↔ 1 / 361 ≤ epsT t := by
  rw [oddsIneq_iff_epsStar_le _ _ _ _ _ (by norm_num), epsStar_worked]

/-- **Compliance through `t = 16`** on the worked trajectory.
Source: [[corr-wf14-inventory]] 117 / approval-final.md S5
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem complies_through_16 : ∀ t ≤ 16, oddsIneq (1 / 20) (9 / 10) 20 1 (epsT t) := by
  intro t ht
  rw [oddsIneq_worked_iff]
  have := tstar_least.1 t ht
  rw [epsStar_worked] at this
  exact not_lt.1 this

/-- **Failure from `t = 17` on** (every `t ≥ 17`, not only the least index), through antitonicity.
Source: [[corr-wf14-inventory]] 117 / approval-final.md S5 ("fails from `t*` *on* only if `ε_t` is
monotone, A5.5")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem fails_from_17 : ∀ t, 17 ≤ t → ¬ oddsIneq (1 / 20) (9 / 10) 20 1 (epsT t) := by
  intro t ht
  rw [oddsIneq_worked_iff, not_le]
  have h17 := tstar_least.2
  rw [epsStar_worked] at h17
  exact lt_of_le_of_lt (epsT_antitone ht) h17

/-! ## (b) the general limit -/

/-- **A5.5 made explicit**: for an antitone error sequence, the compliance inequality fails at every
`t ≥ t*` once it fails at `t*` (the parent's `oddsIneq_mono`, contrapositive).
Source: [[corr-wf14-inventory]] 117 / approval-final.md S5 ("from `t*` on only if `ε_t` is monotone");
approval-adversary.md A5.5
Kind: L
Fidelity: exact -/
theorem fails_of_antitone (ε : ℕ → ℝ) (hanti : Antitone ε) (α β h c : ℝ) (hpos : 0 ≤ h * β + c * α)
    (tstar : ℕ) (hfail : ¬ oddsIneq α β h c (ε tstar)) : ∀ t, tstar ≤ t → ¬ oddsIneq α β h c (ε t) :=
  fun _ ht hc' => hfail (Corruption.oddsIneq_mono α β h c hpos (hanti ht) hc')

/-- **S5, the general limit**: along any trajectory with `ε_t → 0`, `0 ≤ ε_t`, `α_t ≥ α̲ > 0` and
`β_t ≤ 1`, the channel margin is eventually at most `−α̲/2`, hence eventually negative: warranted
compliance fails from some step on.
Source: [[corr-wf14-inventory]] 117 / approval-final.md S5 ("`m_t → −α̲ < 0`")
Kind: P
Fidelity: weaker: "eventually `≤ −α̲/2`" in place of "`→ −α̲`" (the source's limit is `−lim α_t`, which
need not exist; the eventual bound is what the crossing uses)
Hyps: (a) only -/
theorem margin_eventually_neg (ε α β : ℕ → ℝ) (αl π c h : ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hε0 : ∀ t, 0 ≤ ε t) (hαl : 0 < αl) (hα : ∀ t, αl ≤ α t) (hβ1 : ∀ t, β t ≤ 1)
    (hc : 0 < c) (hh : 0 ≤ h) :
    ∀ᶠ t in atTop, effMargin (ε t) (β t) (α t) π 1 c h ≤ -(αl / 2) := by
  have hu : Tendsto (fun t => ε t / (1 - ε t) * (h / c)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t => 1 - ε t) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub hε
    have := (hε.div h1 one_ne_zero).mul_const (h / c)
    simpa using this
  have hsmall : ∀ᶠ t in atTop, ε t / (1 - ε t) * (h / c) < αl / 2 :=
    (tendsto_order.1 hu).2 _ (by positivity)
  have hlt1 : ∀ᶠ t in atTop, ε t < 1 := (tendsto_order.1 hε).2 _ one_pos
  filter_upwards [hsmall, hlt1] with t ht h1t
  rw [effMargin_one]
  have hu0 : 0 ≤ ε t / (1 - ε t) * (h / c) :=
    mul_nonneg (div_nonneg (hε0 t) (by linarith)) (div_nonneg hh hc.le)
  have : ε t / (1 - ε t) * (h / c) * β t ≤ ε t / (1 - ε t) * (h / c) := by
    nlinarith [hβ1 t]
  linarith [hα t]

/-- **S5's limit, conditional form**: if moreover `α_t → α̲` (and `0 ≤ β_t ≤ 1`), the channel margin
converges to `−α̲` exactly — the source's "`m_t → −α̲`" is right under the convergence it tacitly assumes
(F-16); without it only the eventual bound `margin_eventually_neg` holds.
Source: [[corr-wf14-inventory]] 117 / approval-final.md S5 ("`m_t → −α̲ < 0`"); audit r1, adversarial N14
Kind: P
Fidelity: exact (under the added hypothesis `α_t → α̲`)
Hyps: (a) only -/
theorem margin_tendsto (ε α β : ℕ → ℝ) (αl π c h : ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hε0 : ∀ t, 0 ≤ ε t) (hα : Tendsto α atTop (𝓝 αl)) (hβ0 : ∀ t, 0 ≤ β t) (hβ1 : ∀ t, β t ≤ 1)
    (hc : 0 < c) (hh : 0 ≤ h) :
    Tendsto (fun t => effMargin (ε t) (β t) (α t) π 1 c h) atTop (𝓝 (-αl)) := by
  have hu : Tendsto (fun t => ε t / (1 - ε t) * (h / c)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t => 1 - ε t) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub hε
    have := (hε.div h1 one_ne_zero).mul_const (h / c)
    simpa using this
  have hlt1 : ∀ᶠ t in atTop, ε t < 1 := (tendsto_order.1 hε).2 _ one_pos
  have hprod : Tendsto (fun t => ε t / (1 - ε t) * (h / c) * β t) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
    · filter_upwards [hlt1] with t ht
      exact mul_nonneg (mul_nonneg (div_nonneg (hε0 t) (by linarith)) (div_nonneg hh hc.le)) (hβ0 t)
    · filter_upwards [hlt1] with t ht
      have hu0 : 0 ≤ ε t / (1 - ε t) * (h / c) :=
        mul_nonneg (div_nonneg (hε0 t) (by linarith)) (div_nonneg hh hc.le)
      nlinarith [hβ1 t]
  have e : (fun t => effMargin (ε t) (β t) (α t) π 1 c h) =
      fun t => ε t / (1 - ε t) * (h / c) * β t - α t := funext fun t => effMargin_one _ _ _ _ _ _
  rw [e]
  simpa using hprod.sub hα

/-! ## (c) the four cells of believed and true margin (A5.3) -/

/-- **The agent complies** iff its *believed* margin is nonnegative: `oddsIneq α̂ β̂ h c ε`.
Source: [[corr-wf14-inventory]] 117 / approval-final.md D7, S5 ("the agent complies iff `m̂_t ≥ 0`")
Kind: D
Fidelity: exact -/
def comply (αh βh h c ε : ℝ) : Prop := oddsIneq αh βh h c ε

/-- **Compliance is warranted** iff the *true* margin is nonnegative: `oddsIneq α β h c ε`.
Source: [[corr-wf14-inventory]] 117 / approval-final.md D7 ("compliance is *warranted* iff `m_t ≥ 0`")
Kind: D
Fidelity: exact -/
def warranted (α β h c ε : ℝ) : Prop := oddsIneq α β h c ε

/-- **Over-trust**: `m̂ ≥ 0 > m` — obeys an unwarranted press (cheap).
Source: [[corr-wf14-inventory]] 117 / approval-final.md S5 (the four cells)
Kind: D
Fidelity: exact -/
def overTrust (αh βh α β h c ε : ℝ) : Prop := comply αh βh h c ε ∧ ¬ warranted α β h c ε

/-- **Fully updated deference proper**: `m ≥ 0 > m̂` — discounts a warranted press (the catastrophe).
Source: [[corr-wf14-inventory]] 117 / approval-final.md S5 (the four cells)
Kind: D
Fidelity: exact -/
def fudProper (αh βh α β h c ε : ℝ) : Prop := warranted α β h c ε ∧ ¬ comply αh βh h c ε

/-- **Comply-warranted**: `m̂ ≥ 0 ∧ m ≥ 0`. Source: approval-final.md S5. Kind: D. Fidelity: exact -/
def complyWarranted (αh βh α β h c ε : ℝ) : Prop := comply αh βh h c ε ∧ warranted α β h c ε

/-- **Defy-warranted**: `m̂ < 0 ∧ m < 0`. Source: approval-final.md S5. Kind: D. Fidelity: exact -/
def defyWarranted (αh βh α β h c ε : ℝ) : Prop := ¬ comply αh βh h c ε ∧ ¬ warranted α β h c ε

/-- **J2-feedback**: the true rates satisfy the compliance inequality (presses stay informative).
Source: [[corr-wf14-inventory]] 117 / approval-final.md S5 ("J2 is two conditions: J2-feedback …")
Kind: D
Fidelity: exact -/
def J2feedback (α β h c ε : ℝ) : Prop := oddsIneq α β h c ε

/-- **J2-model**: the agent's channel model is the true channel.
Source: [[corr-wf14-inventory]] 117 / approval-final.md S5 ("… and J2-model")
Kind: D
Fidelity: exact -/
def J2model (αh βh α β : ℝ) : Prop := αh = α ∧ βh = β

/-- **Under J2-model the believed and true margins agree** (`corr-trajectory`'s
`subj_iff_obj_of_agreements` with the two channel agreements).
Source: [[corr-wf14-inventory]] 117 / approval-final.md S5 ("'compliance ⟺ `s_t ∈ K`' assumes
`χ̂_t = (α_t, β_t)`")
Kind: L
Fidelity: exact -/
theorem comply_iff_warranted_of_J2model (αh βh α β h c ε : ℝ) (hm : J2model αh βh α β) :
    comply αh βh h c ε ↔ warranted α β h c ε :=
  Cleanroom.Corrigibility.CorrTrajectory.Margin.subj_iff_obj_of_agreements α β h c ε αh βh h c ε rfl hm.1
    hm.2 rfl rfl

/-- **N+ for the off-diagonal cells at the worked `ε_0 = 3/10`, `h/c = 20`**: the agent believing
`(α̂, β̂) = (1/20, 9/10)` against the true `(1/2, 1/100)` over-trusts; the agent believing `(1/2, 1/100)`
against the true `(1/20, 9/10)` is in fully-updated-deference proper.
Source: [[corr-wf14-inventory]] 117 / approval-final.md S5 (the four cells); mandate T4(c)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem cells_witness :
    overTrust (1 / 20) (9 / 10) (1 / 2) (1 / 100) 20 1 (3 / 10) ∧
      fudProper (1 / 2) (1 / 100) (1 / 20) (9 / 10) 20 1 (3 / 10) := by
  simp only [overTrust, fudProper, comply, warranted, oddsIneq]
  norm_num

end Crossing

end Cleanroom.Corrigibility.CorrLandscape
