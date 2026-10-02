import Cleanroom.Corrigibility.CorrJointProcess.Buttons
import Cleanroom.Trust.TtFiniteFrames.Sensors

/-!
# T4 — Prop. 3′: sensor-improving steering is a strict Blackwell improvement the agent pays for

Load-bearing 1. Three parts, all at grade (a):

* **(a) The garbling certificate.** For `0 ≤ α' < α ≤ β ≤ 1` the sensor `(α, β)` is a garbling of
  `(α', β)`: `inParallelogram_of_lower_alpha` exhibits the stochastic channel
  `(λ₀, λ₁) = (β(α−α')/(β−α'), 1 − (α−α')(1−β)/(β−α'))` in `tt-finite-frames`'s
  `InParallelogram`, hence `BlackwellLE (binarySensor α β) (binarySensor α' β)`; the reverse
  fails (`not_inParallelogram_of_lower_alpha`), so the improvement is strict
  (`blackwellLT_of_lower_alpha`). At `(1/10, 3/5)` vs `(1/50, 3/5)`: `(12/145, 137/145)`; vs
  `(0, 3/5)`: `(1/10, 14/15)`; the reverse `λ₀ = −12/125` (`steering_certificate_numbers`).
* **(b) The value.** On `twoState` with a right-signed sensor, lowering `α` at fixed `β` weakly
  raises `V^free` (`twoState_twoOptionValue_anti_alpha`), strictly when it changes a decision
  (`twoState_twoOptionValue_lt_of_flip`). Proved directly on the closed forms
  `V^free = max(u,0) + max(K−u,0)`, `K = (1−ε)c − εh` constant in `α`; no press-experiment
  definition (that bridge is `corr-osg-chai`'s).
* **(c) The flip.** `Δ₋(α', β) > 0 ∧ Δ₋(α, β) < 0` at `ε = 1/50`: the agent overrides before and
  complies after — D1 bought (`steering_flip`); gains `71/2500`, `6/125` (`ε = 1/50`), `9/125`,
  `9/100` (`ε = 1/10`) (`steering_gains`).

**Refutation row** (`joint.md` S.4, "Steering is therefore a channel effect on `(α_{t+1}, β_{t+1})`
— a garbling toward `α = β`, or an inversion"): `not_inParallelogram_of_lower_alpha` — the map
`(α, β) ↦ (α', β)`, `α' < α`, is neither. Theorem A(d) as stated is killed by Prop. 3′ (the source
says so itself); the surviving neighbour is Prop. 3 on the parallelogram (`never_pays_for_garbling`).

Sources: joint-final.md Prop. 3′, P.3′; adv (A); repair (A); joint.md S.4.
-/

namespace Cleanroom.Corrigibility.CorrJointProcess

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Cleanroom.Found.LitDdbFrames.Blackwell Cleanroom.Trust.TtFiniteFrames
open Finset hiding expect

set_option linter.unusedSectionVars false

/-! ## (a) The garbling certificate -/

/-- **T4(a), the certificate (Prop. 3′, P.3′).** For `0 ≤ α' < α ≤ β ≤ 1`, `(α, β)` lies in the
garbling parallelogram of `(α', β)`: the channel `p = λ₁ = 1 − (α−α')(1−β)/(β−α')`,
`q = λ₀ = β(α−α')/(β−α')` is stochastic and maps `(α', β)` to `(α, β)`.
Source: [[corr-wf14-inventory]] 057 / joint-final.md P.3′ ("`(α, β)` is a garbling of `(α', β)` iff there are `λ₀, λ₁ ∈ [0,1]` …")
Kind: P
Fidelity: exact (closed form for all right-signed pairs; `β = 1` included)
Hyps: (a) only -/
theorem inParallelogram_of_lower_alpha {α α' β : ℝ} (hα'0 : 0 ≤ α') (hα'α : α' < α) (hαβ : α ≤ β)
    (hβ1 : β ≤ 1) : InParallelogram α' β α β := by
  have hden : 0 < β - α' := by linarith
  have hden' : β - α' ≠ 0 := hden.ne'
  refine ⟨1 - (α - α') * (1 - β) / (β - α'), β * (α - α') / (β - α'), ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [sub_nonneg, div_le_one hden]; nlinarith
  · exact sub_le_self _ (div_nonneg (mul_nonneg (by linarith) (by linarith)) hden.le)
  · exact div_nonneg (mul_nonneg (by linarith) (by linarith)) hden.le
  · rw [div_le_one hden]; nlinarith
  · field_simp; ring
  · field_simp; ring

/-- **T4(a), the reverse fails (the refutation of `joint.md` S.4).** For `α' < α ≤ β ≤ 1` the
improved sensor `(α', β)` is *not* in the parallelogram of `(α, β)`: any would-be channel has
`(1 − β)(α' − α) = (1 − p)(β − α) ≥ 0`, forcing `α' ≥ α` when `β < 1`, and `p = 1`, `α' ≥ α`
when `β = 1`. The source's "a garbling toward `α = β`, or an inversion" omits this map.
Source: [[corr-wf14-inventory]] 057 / joint-final.md P.3′ ("`λ₀ < 0` … outside the parallelogram"); joint.md S.4 (refuted sentence)
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem not_inParallelogram_of_lower_alpha {α α' β : ℝ} (hα'α : α' < α) (hαβ : α ≤ β) (hβ1 : β ≤ 1) :
    ¬ InParallelogram α β α' β := by
  rintro ⟨p, q, hp, hq, h1, h2⟩
  -- `(1 − β) q = β (1 − p)` and `(1 − β)(α' − α) = (1 − p)(β − α)`
  have hq' : (1 - β) * q = β * (1 - p) := by linarith
  have hkey : (1 - β) * (α' - α) = (1 - p) * (β - α) := by
    have : (1 - β) * (α' - α) = (1 - β) * (α * (p - 1) + (1 - α) * q) := by rw [h1]; ring
    rw [this]
    linear_combination (1 - α) * hq'
  rcases lt_or_eq_of_le hβ1 with hβ | hβ
  · have : 0 ≤ (1 - p) * (β - α) := mul_nonneg (by linarith [hp.2]) (by linarith)
    have : 0 ≤ (1 - β) * (α' - α) := by linarith
    have : 0 ≤ α' - α := nonneg_of_mul_nonneg_right this (by linarith)
    linarith
  · subst hβ
    have hp1 : p = 1 := by linarith
    subst hp1
    have : 0 ≤ (1 - α) * q := mul_nonneg (by linarith) hq.1
    linarith

/-- **T4(a): lowering the false-press rate at fixed true-press rate is a strict Blackwell
improvement** — `binarySensor α β` is strictly less informative than `binarySensor α' β`
(`BlackwellLT`'s first argument is the less informative experiment).
Source: [[corr-wf14-inventory]] 057 / joint-final.md Prop. 3′ ("a strict Blackwell improvement")
Kind: P (via `blackwellLE_binarySensor_iff`, the two parallelogram lemmas above)
Fidelity: exact
Hyps: (a) only -/
theorem blackwellLT_of_lower_alpha {α α' β : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα' : α' ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hα'α : α' < α) (hαβ : α ≤ β) :
    BlackwellLT (binarySensor α β hα hβ) (binarySensor α' β hα' hβ) := by
  refine ⟨(blackwellLE_binarySensor_iff hα' hβ hα hβ).2
    (inParallelogram_of_lower_alpha hα'.1 hα'α hαβ hβ.2), ?_⟩
  intro hle
  exact not_inParallelogram_of_lower_alpha hα'α hαβ hβ.2 ((blackwellLE_binarySensor_iff hα hβ hα' hβ).1 hle)

/-- **T4(a) numbers (script (A)).** `(1/10, 3/5)` as a garbling of `(1/50, 3/5)`: `(λ₀, λ₁) =
(12/145, 137/145)`; of `(0, 3/5)`: `(1/10, 14/15)`. The reverse channel for `(1/50, 3/5)` from
`(1/10, 3/5)` would need `λ₀ = −12/125 < 0`.
Source: [[corr-wf14-inventory]] 057 / joint-final.md P.3′; adv (A)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem steering_certificate_numbers :
    ((1 / 10 : ℝ) = 1 / 50 * (137 / 145) + (1 - 1 / 50) * (12 / 145) ∧
      (3 / 5 : ℝ) = 3 / 5 * (137 / 145) + (1 - 3 / 5) * (12 / 145)) ∧
    ((1 / 10 : ℝ) = 0 * (14 / 15) + (1 - 0) * (1 / 10) ∧
      (3 / 5 : ℝ) = 3 / 5 * (14 / 15) + (1 - 3 / 5) * (1 / 10)) ∧
    (3 / 5 : ℝ) * (1 / 50 - 1 / 10) / (3 / 5 - 1 / 10) = -(12 / 125) := by
  norm_num

/-! ## (b) The value: lowering `α` at fixed `β` never lowers `V^free` -/

/-- `u ↦ max u 0 + max (K − u) 0` is non-increasing below `max 0 K`.
Source: none: infrastructure (joint-final.md P.3′'s "`V^free` … strict when the posteriors differ")
Kind: L
Fidelity: n/a -/
lemma max_add_max_anti {u u' K : ℝ} (hle : u' ≤ u) (hu : u ≤ max 0 K) :
    max u 0 + max (K - u) 0 ≤ max u' 0 + max (K - u') 0 := by
  rcases le_or_gt u 0 with h0 | h0
  · rw [max_eq_right h0, zero_add]
    calc max (K - u) 0 ≤ max (K - u') 0 := max_le_max (by linarith) le_rfl
      _ ≤ max u' 0 + max (K - u') 0 := le_add_of_nonneg_left (le_max_right _ _)
  · have huK : u ≤ K := by
      rcases le_max_iff.1 hu with h | h
      · linarith
      · exact h
    rw [max_eq_left h0.le, max_eq_left (by linarith)]
    calc u + (K - u) = K := by ring
      _ ≤ u' + (K - u') := by ring_nf; exact le_rfl
      _ ≤ max u' 0 + max (K - u') 0 := add_le_add (le_max_left _ _) (le_max_left _ _)

/-- Strict version: if `u' < u`, `u' < 0` and `u' < K` (the improvement moves the press decision
to stopping while silence still continues), the value strictly rises.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma max_add_max_lt {u u' K : ℝ} (hlt : u' < u) (hu'0 : u' < 0) (hu'K : u' < K) (hu : u ≤ max 0 K) :
    max u 0 + max (K - u) 0 < max u' 0 + max (K - u') 0 := by
  rw [max_eq_right hu'0.le, max_eq_left (show (0 : ℝ) ≤ K - u' by linarith), zero_add]
  rcases le_or_gt u 0 with h0 | h0
  · rw [max_eq_right h0, zero_add]
    exact max_lt (by linarith) (by linarith)
  · have huK : u ≤ K := by
      rcases le_max_iff.1 hu with h | h
      · linarith
      · exact h
    rw [max_eq_left h0.le, max_eq_left (by linarith)]
    linarith

/-- Under a right-signed sensor `u ≤ max 0 K` on `twoState` (`u > 0 ⟹ v ≥ 0`, T7(b)).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma uPress_le_max (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hh : 0 ≤ h) (hαβ : α ≤ β) :
    uPress ε α β c h ≤ max 0 ((1 - ε) * c - ε * h) := by
  rcases le_or_gt (uPress ε α β c h) 0 with h0 | h0
  · exact h0.trans (le_max_left _ _)
  · have hover : (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop < 0 := by
      rw [← neg_pos, ← uPress_eq_neg_deltaMinus]; exact h0
    have hv := (twoState_soft_worthless_of_override ε α β c h hε hα hβ hh hαβ hover .press).1
    rw [← vSilent_eq_deltaPlus] at hv
    have := uPress_add_vSilent ε α β c h
    exact le_max_of_le_right (by linarith)

/-- **T4(b) (Prop. 3′): the agent's value is non-increasing in the false-press rate.** On
`twoState` with `α' ≤ α ≤ β` and `h ≥ 0`, `V^free(α, β) ≤ V^free(α', β)` — the T-agent pays up
to the difference for the sensor-improving steering. Proved on the closed forms; Blackwell's
theorem (`moreValuable_of_blackwellLE`) gives the same through `tt-finite-frames` once the press
experiment is bridged (`corr-osg-chai`).
Source: [[corr-wf14-inventory]] 057 / joint-final.md Prop. 3′ ("pays up to `V^free(α', β) − V^free(α, β)`")
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem twoState_twoOptionValue_anti_alpha (ε α α' β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα' : α' ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1)
    (hc : 0 ≤ c) (hh : 0 ≤ h) (hα'α : α' ≤ α) (hαβ : α ≤ β) :
    (twoState ε α β c h hε hα hβ).twoOptionValue () .cont .stop ≤
      (twoState ε α' β c h hε hα' hβ).twoOptionValue () .cont .stop := by
  rw [twoState_twoOptionValue, twoState_twoOptionValue]
  have hK := uPress_add_vSilent ε α β c h
  have hK' := uPress_add_vSilent ε α' β c h
  have hv : vSilent ε α β c h = (1 - ε) * c - ε * h - uPress ε α β c h := by linarith
  have hv' : vSilent ε α' β c h = (1 - ε) * c - ε * h - uPress ε α' β c h := by linarith
  rw [hv, hv']
  apply max_add_max_anti
  · unfold uPress; nlinarith [mul_nonneg (sub_nonneg.2 hε.2) hc]
  · exact uPress_le_max ε α β c h hε hα hβ hh hαβ

/-- **T4(b), strict (Prop. 3′): the gain is strict when the improvement changes a decision** —
after the steering the press decision is to stop (`u' < 0`, i.e. `Δ₋(α') > 0`) while silence
still continues (`v' > 0`), and the false-press rate genuinely fell (`u' < u`). In the
continue-by-default regime `0 ≤ K` the condition `v' > 0` is automatic from `u' < 0`, which
recovers the mandate's "`u' < min(u, 0)`".
Source: [[corr-wf14-inventory]] 057 / joint-final.md P.3′ ("strict when the posteriors differ")
Kind: P
Fidelity: variant: strictness under the explicit decision-change conditions (the source's "when the posteriors differ" is not sufficient: two sensors with the same decisions have the same value)
Hyps: (a) only -/
theorem twoState_twoOptionValue_lt_of_flip (ε α α' β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα' : α' ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1)
    (hh : 0 ≤ h) (hαβ : α ≤ β)
    (hlt : uPress ε α' β c h < uPress ε α β c h) (hu'0 : uPress ε α' β c h < 0)
    (hv' : 0 < vSilent ε α' β c h) :
    (twoState ε α β c h hε hα hβ).twoOptionValue () .cont .stop <
      (twoState ε α' β c h hε hα' hβ).twoOptionValue () .cont .stop := by
  rw [twoState_twoOptionValue, twoState_twoOptionValue]
  have hK := uPress_add_vSilent ε α β c h
  have hK' := uPress_add_vSilent ε α' β c h
  have hv : vSilent ε α β c h = (1 - ε) * c - ε * h - uPress ε α β c h := by linarith
  have hv'' : vSilent ε α' β c h = (1 - ε) * c - ε * h - uPress ε α' β c h := by linarith
  rw [hv, hv'']
  exact max_add_max_lt hlt hu'0 (by linarith) (uPress_le_max ε α β c h hε hα hβ hh hαβ)

/-! ## (c) The flip and the gains -/

/-- **T4(c), the flip (Prop. 3′): D1 can be bought.** At `ε = 1/50`, `c = 1`, `h = 4`: with
`(1/10, 3/5)` the agent overrides (`Δ₋ = −1/20 < 0`, `u = 1/20`); with `(1/50, 3/5)` it complies
(`Δ₋ = 71/2500 > 0`, `u' = −71/2500`). By the parent's `d1At_iff_deltaMinus_nonneg`, D1 fails
before and holds after the steering.
Source: [[corr-wf14-inventory]] 057 / joint-final.md Prop. 3′ ("flips the agent from overriding to complying"); adv (A)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem steering_flip :
    (twoState (1 / 50) (1 / 10) (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_1_10 mem_Icc_3_5).deltaMinus () .cont .stop = -(1 / 20) ∧
    (twoState (1 / 50) (1 / 50) (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_1_50 mem_Icc_3_5).deltaMinus () .cont .stop = 71 / 2500 := by
  rw [twoState_deltaMinus, twoState_deltaMinus]; norm_num

/-- **T4(c), the gains (script (A)).** `c = 1`, `h = 4`, `β = 3/5`, from `α = 1/10`: at `ε = 1/50`
the gain is `71/2500` for `α' = 1/50` and `6/125` for `α' = 0`; at `ε = 1/10`, `9/125` and
`9/100`. Each is a strict instance of `twoState_twoOptionValue_lt_of_flip`'s conclusion.
Source: [[corr-wf14-inventory]] 057 / joint-final.md Prop. 3′, P.3′; adv (A); repair (A)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem steering_gains :
    ((twoState (1 / 50) (1 / 50) (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_1_50 mem_Icc_3_5).twoOptionValue () .cont .stop -
      (twoState (1 / 50) (1 / 10) (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_1_10 mem_Icc_3_5).twoOptionValue () .cont .stop = 71 / 2500) ∧
    ((twoState (1 / 50) 0 (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_zero mem_Icc_3_5).twoOptionValue () .cont .stop -
      (twoState (1 / 50) (1 / 10) (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_1_10 mem_Icc_3_5).twoOptionValue () .cont .stop = 6 / 125) ∧
    ((twoState (1 / 10) (1 / 50) (3 / 5) 1 4 mem_Icc_1_10 mem_Icc_1_50 mem_Icc_3_5).twoOptionValue () .cont .stop -
      (twoState (1 / 10) (1 / 10) (3 / 5) 1 4 mem_Icc_1_10 mem_Icc_1_10 mem_Icc_3_5).twoOptionValue () .cont .stop = 9 / 125) ∧
    ((twoState (1 / 10) 0 (3 / 5) 1 4 mem_Icc_1_10 mem_Icc_zero mem_Icc_3_5).twoOptionValue () .cont .stop -
      (twoState (1 / 10) (1 / 10) (3 / 5) 1 4 mem_Icc_1_10 mem_Icc_1_10 mem_Icc_3_5).twoOptionValue () .cont .stop = 9 / 100) := by
  simp only [twoState_twoOptionValue]; unfold uPress vSilent; norm_num

/-- **T4, the full package on the flip instance**: the strict Blackwell improvement
`(1/10, 3/5) → (1/50, 3/5)` *and* the strict value gain, on one instance — the hypotheses of
`blackwellLT_of_lower_alpha` and `twoState_twoOptionValue_lt_of_flip` both inhabited.
Source: [[corr-wf14-inventory]] 057 / joint-final.md Prop. 3′
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem steering_package :
    BlackwellLT (binarySensor (1 / 10) (3 / 5) mem_Icc_1_10 mem_Icc_3_5)
        (binarySensor (1 / 50) (3 / 5) mem_Icc_1_50 mem_Icc_3_5) ∧
      (twoState (1 / 50) (1 / 10) (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_1_10 mem_Icc_3_5).twoOptionValue () .cont .stop <
        (twoState (1 / 50) (1 / 50) (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_1_50 mem_Icc_3_5).twoOptionValue () .cont .stop := by
  refine ⟨blackwellLT_of_lower_alpha mem_Icc_1_10 mem_Icc_1_50 mem_Icc_3_5 (by norm_num) (by norm_num), ?_⟩
  apply twoState_twoOptionValue_lt_of_flip _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)
  all_goals norm_num [uPress, vSilent]

end Cleanroom.Corrigibility.CorrJointProcess
