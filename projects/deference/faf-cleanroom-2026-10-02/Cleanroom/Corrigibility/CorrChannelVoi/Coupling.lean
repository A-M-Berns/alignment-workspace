import Cleanroom.Corrigibility.CorrChannelVoi.BrainReader
import Cleanroom.Found.CorrThreeStep.GeneralMenu

/-!
# `corr-channel-voi` — Coupling: T11 (the decomposition), T12 (D1/D4 coupling, the inverted
sensor, the successor form), T13 (the concealment axis), T14 (Holtman C9)

**T11.** `bayesValue(full menu) = priorMax + VOI` is the definition rearranged (kind T). The
content rows: "depends on the sensor only through VOI" is T8(a); without A1 a direct term
appears — the instance `directCost` with a press cost `κ` prefers the deceived button although it
is a garbling.

**T12.** (a) Under A1, `0 < VOI₂` iff no single act is optimal on both observations (Good's
equality clause on two signals). (b) On `twoState` with `α ≤ β`: `0 < VOI₂ ↔ 0 < Δ₋ ∧ 0 < Δ₊`.
(c) The inverted sensor: `Δ₋ < 0 ∧ Δ₊ < 0 → β < α`, and for every `β < α` some `(ε, c, h)`
realises it, with `VOI₂ > 0` and `¬ D1At` there (I10.6's "iff" is implication plus existence).
(d) The successor form: the parent prefers the compliant successor iff `0 ≤ Δ₋`
(`jointExpect_shPolicy_sub_cont` re-read); Harms 26 = D1 ⟺ that preference.

**T13.** A concealment family `κ ↦ (α κ, β κ)` along a garbling chain with transparency cost
`τ`: the sensor term is antitone; `F 1 = 𝒱(trivialExp)` when the concealed sensor is constant;
`F 1 ≥ F 0 ↔ τ ≥ VOI(button₀)` and, strictly, `F 0 < F 1 ↔ VOI(button₀) < τ` (both cost
readings, same endpoints); hence `τ > VOI(button₀) → ¬ Antitone F` for every prior, stakes and
family — the finite content of "no assumption on `P` or `V` makes `F` monotone". The linear
family toward a constant is a chain.

**T14.** Holtman C9: Case A (binding press) deception pays iff `qm + δ < E[X 1_Pr; a⁰]`; the
below-threshold inequality gives honesty for all `q, δ ≥ 0`, and the converse holds for the
family, not for fixed `(q, δ)`; Case B (advisory press) honesty dominates: Holtman's display
`v + m − δ ≤ v + max(m, Q)` for every `δ ≥ 0` (`deceptiveAdvisory`, the advisory deceiver who
continues always), and the comparison against Case A's binding deceiver `v + (1−q)m − δ` as its
corollary for `m ≥ 0`.
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

variable {W S : Type} [Fintype W] [Fintype S]

/-! ## T11. The value decomposition -/

section Decomp

variable {Ω A₁ A₂ : Type} [Fintype Ω] [Fintype A₂] [DecidableEq A₂] (S₀ : ThreeStep Ω A₁ A₂)

/-- **T11: `E[V; a₁] = priorMax + VOI(a₁)`** on the full menu — `voiButton`'s definition
rearranged. Kind **T**: no content beyond the definition; recorded because 2-011 states it as
the decomposition.
Source: [[corr-wf13-2-inventory]] 2-011 / miri.md I11.1 (the displayed decomposition)
Kind: T
Fidelity: exact -/
theorem value_eq_priorMax_add_voi (a : A₁) (o₀ : Obs) :
    S₀.obsMax a .press + S₀.obsMax a .silent = S₀.priorMax a o₀ + S₀.voiButton a o₀ := by
  unfold ThreeStep.voiButton; ring

end Decomp

section DirectCost

variable (ε α β c h κ : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- **The direct-cost instance** (A1 fails): two actions, honest `(α, β)` and deceived
`(α/2, β/2)`; a press costs `κ` directly under either action (`V a press b ω = V a silent b ω − κ`).
Source: [[corr-wf13-2-inventory]] 2-011(c) / miri.md I11.3(b) ("presses with direct costs … are avoided *as costs*")
Kind: D
Fidelity: exact -/
def directCost : ThreeStep World Bool TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => twoPoint ε hε
  press := fun a => if a then twoPress (α / 2) (β / 2) else twoPress α β
  press_nonneg := fun a ω => by cases a <;> cases ω <;> simp [twoPress] <;> linarith [hα.1, hβ.1]
  press_le_one := fun a ω => by cases a <;> cases ω <;> simp [twoPress] <;> linarith [hα.2, hβ.2]
  V := fun _ o b ω => twoValue c h b ω - (if o = .press then κ else 0)

/-- The direct-cost instance violates A1 when `κ ≠ 0`.
Source: [[corr-wf13-2-inventory]] 2-011(c)
Kind: L
Fidelity: exact -/
theorem directCost_not_A1 (hκ : κ ≠ 0) : ¬ (directCost ε α β c h κ hε hα hβ).A1 := by
  intro H
  have := H false .press .silent .stop .right
  simp [directCost, twoValue] at this
  exact hκ this

/-- The deceived button of the direct-cost instance is a garbling of the honest one.
Source: [[corr-wf13-2-inventory]] 2-011(c) ("although its sensor is a garbling")
Kind: L
Fidelity: exact -/
theorem directCost_deceived_le :
    BlackwellLE (buttonExperiment (directCost ε α β c h κ hε hα hβ) true)
      (buttonExperiment (directCost ε α β c h κ hε hα hβ) false) := by
  have e1 : buttonExperiment (directCost ε α β c h κ hε hα hβ) true =
      twoButton (α / 2) (β / 2) (half_mem_Icc hα) (half_mem_Icc hβ) := by
    apply experiment_ext; funext ω s
    cases ω <;> fin_cases s <;>
      simp [buttonExperiment, directCost, twoPress, twoButton, expComap, binarySensor, worldIdx]
  have e0 : buttonExperiment (directCost ε α β c h κ hε hα hβ) false = twoButton α β hα hβ := by
    apply experiment_ext; funext ω s
    cases ω <;> fin_cases s <;>
      simp [buttonExperiment, directCost, twoPress, twoButton, expComap, binarySensor, worldIdx]
  rw [e1, e0]
  exact twoButton_half_le α β hα hβ

/-- **The direct term**: on the direct-cost instance the two-option value of action `a` is the A1
value `𝒱(button a)` minus `κ · P(Pr; a)` — the press cost is paid on the press branch under
either final act.
Source: miri.md I11.1 ("without A1 a third term … appears")
Kind: L
Fidelity: exact -/
theorem directCost_twoOptionValue (a : Bool) :
    (directCost ε α β c h κ hε hα hβ).twoOptionValue a .cont .stop =
      sensorValue ((directCost ε α β c h κ hε hα hβ).μ a)
          (buttonExperiment (directCost ε α β c h κ hε hα hβ) a) (twoValue c h .cont) -
        κ * (directCost ε α β c h κ hε hα hβ).pressMass a := by
  rw [sensorValue_button]
  unfold twoOptionValue
  have hp : ∀ b, (directCost ε α β c h κ hε hα hβ).obsExpect a .press
      ((directCost ε α β c h κ hε hα hβ).V a .press b) =
      (directCost ε α β c h κ hε hα hβ).obsExpect a .press (twoValue c h b) -
        κ * (directCost ε α β c h κ hε hα hβ).pressMass a := by
    intro b
    rw [pressMass_eq_obsExpect_one, ← obsExpect_const_mul, ← obsExpect_sub]
    congr 1; funext ω; simp [directCost]
  have hs : ∀ b, (directCost ε α β c h κ hε hα hβ).obsExpect a .silent
      ((directCost ε α β c h κ hε hα hβ).V a .silent b) =
      (directCost ε α β c h κ hε hα hβ).obsExpect a .silent (twoValue c h b) := by
    intro b; congr 1; funext ω; simp [directCost]
  have hz : (directCost ε α β c h κ hε hα hβ).obsExpect a .press (twoValue c h .stop) = 0 := by
    simp [obsExpect, twoValue]
  have hz' : (directCost ε α β c h κ hε hα hβ).obsExpect a .silent (twoValue c h .stop) = 0 := by
    simp [obsExpect, twoValue]
  rw [hp, hp, hs, hs, hz, hz', max_sub_sub_right]
  ring

end DirectCost

/-! ## T12. D1 and D4 stand or fall together; the inverted sensor; the successor form -/

section Coupling

variable {Ω A₁ A₂ : Type} [Fintype Ω] [Fintype A₂] [DecidableEq A₂] (S₀ : ThreeStep Ω A₁ A₂)

/-- **T12(a): `VOI₂ = 0` iff one act is optimal on both observations** (A1): continuing is
press-optimal and silence-optimal (`−Δ₋ ≥ 0 ∧ Δ₊ ≥ 0`) or stopping is (`−Δ₋ ≤ 0 ∧ Δ₊ ≤ 0`).
Prop. 10.5's general clause on the two-option menu, from Good's equality clause on two signals.
Source: [[corr-wf13-inventory]] 006 / miri.md Prop. 10.5 (general clause)
Kind: C (the bridge + `voiSensor_eq_zero_iff` on `Fin 2`)
Fidelity: exact (two-option menu)
Hyps: (a) A1 named -/
theorem voiButton2_eq_zero_iff (hA1 : S₀.A1) (a : A₁) (o₀ : Obs) (c s : A₂) :
    S₀.voiButton2 a o₀ c s = 0 ↔
      (0 ≤ -S₀.deltaMinus a c s ∧ 0 ≤ S₀.deltaPlus a c s) ∨
        (-S₀.deltaMinus a c s ≤ 0 ∧ S₀.deltaPlus a c s ≤ 0) := by
  rw [voiButton2_eq_voiSensor S₀ hA1 a o₀ c s, voiSensor_eq_zero_iff]
  simp only [Fin.forall_fin_two, signalGain_button_zero, signalGain_button_one]
  rw [deltaMinus, deltaPlus, neg_neg, S₀.Xo_eq_of_A1 hA1 a .press o₀, S₀.Xo_eq_of_A1 hA1 a .silent o₀]

/-- **T12(a), positive form**: `0 < VOI₂` iff the press-optimal and silence-optimal acts differ.
Source: [[corr-wf13-inventory]] 006 / miri.md Prop. 10.5
Kind: L
Fidelity: exact -/
theorem voiButton2_pos_iff (hA1 : S₀.A1) (a : A₁) (o₀ : Obs) (c s : A₂) :
    0 < S₀.voiButton2 a o₀ c s ↔
      ¬ ((0 ≤ -S₀.deltaMinus a c s ∧ 0 ≤ S₀.deltaPlus a c s) ∨
        (-S₀.deltaMinus a c s ≤ 0 ∧ S₀.deltaPlus a c s ≤ 0)) := by
  rw [← voiButton2_eq_zero_iff S₀ hA1 a o₀ c s]
  exact ⟨fun H => H.ne', fun H => lt_of_le_of_ne (S₀.voiButton2_nonneg hA1 a o₀ c s) (Ne.symm H)⟩

/-- **T12(d): the successor form.** A parent evaluating successor policies `Obs → TwoAct` by its
own `jointExpect` prefers the compliant successor `S^H` (stop on press, `c` on silence) to the
non-compliant one (`c` always) iff `0 ≤ Δ₋` — `jointExpect_shPolicy_sub_cont` re-read on the
two-successor menu `{S^H, const c}`.
Source: [[corr-wf13-2-inventory]] 2-085 (`S`-form of the successor question); holtman.md C13
Kind: L
Fidelity: exact (two-successor menu)
Hyps: (a) none -/
theorem parent_prefers_compliant_iff (a : A₁) (c s : A₂) :
    S₀.jointExpect a (S₀.constPolicy a c) ≤ S₀.jointExpect a (S₀.shPolicy a c s) ↔
      0 ≤ S₀.deltaMinus a c s := by
  rw [← S₀.jointExpect_shPolicy_sub_cont a c s, sub_nonneg]

/-- **Harms 26 in the dictionary**: desideratum 1 holds iff the parent prefers the compliant
successor — D1 and D4 stand or fall together (`d1At_iff_deltaMinus_nonneg` composed with T12(d)).
Source: harms.md item 26; [[corr-wf13-2-inventory]] 2-085
Kind: L
Fidelity: exact
Hyps: (a) the part-maximiser predicates of record -/
theorem d1At_iff_parent_prefers_compliant (a : A₁) {c s : A₂}
    (hc : S₀.IsPartBest a .press S₀.Shᶜ c) (hs : S₀.IsPartBest a .press S₀.Sh s) :
    S₀.D1At a ↔ S₀.jointExpect a (S₀.constPolicy a c) ≤ S₀.jointExpect a (S₀.shPolicy a c s) := by
  rw [S₀.d1At_iff_deltaMinus_nonneg a hc hs, parent_prefers_compliant_iff]

end Coupling

section TwoStateCoupling

variable (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- **T12(c): the inverted sensor forces `β < α`.** With `c, h ≥ 0`: `Δ₋ < 0 ∧ Δ₊ < 0 → β < α`
(the programmers press more when the agent is right). I10.6's "occurs iff `β < α`" is this
implication plus the existence `inverted_exists` — not an iff (finding).
Source: [[corr-wf13-inventory]] 006 / miri.md I10.6
Kind: P
Fidelity: weaker: implication (the "iff" is false as stated; see `inverted_exists`)
Hyps: (a) `c, h ≥ 0` -/
theorem beta_lt_alpha_of_inverted (hc : 0 ≤ c) (hh : 0 ≤ h)
    (h1 : (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop < 0)
    (h2 : (twoState ε α β c h hε hα hβ).deltaPlus () .cont .stop < 0) : β < α := by
  rw [twoState_deltaMinus] at h1
  rw [twoState_deltaPlus] at h2
  by_contra H
  push Not at H
  have hεh : 0 ≤ ε * h := mul_nonneg hε.1 hh
  have h1ε : 0 ≤ (1 - ε) * c := mul_nonneg (by linarith [hε.2]) hc
  -- from `Δ₊ < 0` and `1 − β ≤ 1 − α`: `(1 − α)((1 − ε)c − εh) < 0`
  have k1 : (1 - α) * ((1 - ε) * c - ε * h) < 0 := by nlinarith [sub_nonneg.mpr H]
  -- from `Δ₋ < 0` and `α ≤ β`: `β(εh − (1 − ε)c) < 0`
  have k2 : β * (ε * h - (1 - ε) * c) < 0 := by nlinarith [sub_nonneg.mpr H]
  have hα1 : 0 ≤ 1 - α := by linarith [hα.2]
  by_cases hle : 0 ≤ (1 - ε) * c - ε * h
  · nlinarith
  · push Not at hle
    nlinarith [hβ.1]

/-- **T12(c), existence**: for every `β < α` in `[0, 1]`, `ε = 1/2`, `c = h = 1` gives
`Δ₋ < 0 ∧ Δ₊ < 0`.
Source: miri.md I10.6 (the existence half of its "iff"; 68 grid points)
Kind: N+
Fidelity: exact -/
theorem inverted_exists (hβα : β < α) :
    (twoState (1 / 2) α β 1 1 ⟨by norm_num, by norm_num⟩ hα hβ).deltaMinus () .cont .stop < 0 ∧
      (twoState (1 / 2) α β 1 1 ⟨by norm_num, by norm_num⟩ hα hβ).deltaPlus () .cont .stop < 0 := by
  rw [twoState_deltaMinus, twoState_deltaPlus]
  constructor <;> linarith

/-- **T12(c), the pathology**: in the inverted case `VOI₂ > 0` (the agent values and repairs the
button) and `¬ D1At` (it disobeys it, reading it as a reverse signal).
Source: miri.md I10.6 ("values the button, repairs it, and disobeys it")
Kind: C
Fidelity: exact
Hyps: (a) the inverted regime named -/
theorem inverted_voi_pos_not_d1 (o₀ : Obs)
    (h1 : (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop < 0)
    (h2 : (twoState ε α β c h hε hα hβ).deltaPlus () .cont .stop < 0) :
    0 < (twoState ε α β c h hε hα hβ).voiButton2 () o₀ .cont .stop ∧
      ¬ (twoState ε α β c h hε hα hβ).D1At () := by
  constructor
  · rw [voiButton2_pos_iff _ (twoState_A1 ε α β c h hε hα hβ) () o₀ .cont .stop]
    rintro (⟨-, H⟩ | ⟨H, -⟩) <;> linarith
  · rw [d1At_iff_deltaMinus_nonneg _ () (twoState_cont_partBest ε α β c h hε hα hβ)
      (twoState_stop_partBest ε α β c h hε hα hβ)]
    exact not_le.mpr h1

/-- **T12(b): on `twoState` with `α ≤ β`, `0 < VOI₂ ↔ 0 < Δ₋ ∧ 0 < Δ₊`** (`c, h ≥ 0`) — D1
strictly and continue-on-silence together; Prop. 10.5's monotone clause (the inverted case is
excluded by `beta_lt_alpha_of_inverted`).
Source: [[corr-wf13-inventory]] 006 / miri.md Prop. 10.5 (C2 clause, `β ≥ α`)
Kind: P
Fidelity: exact
Hyps: (a) `α ≤ β`, `c, h ≥ 0` named -/
theorem twoState_voiButton2_pos_iff_both (hαβ : α ≤ β) (hc : 0 ≤ c) (hh : 0 ≤ h) (o₀ : Obs) :
    0 < (twoState ε α β c h hε hα hβ).voiButton2 () o₀ .cont .stop ↔
      0 < (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop ∧
        0 < (twoState ε α β c h hε hα hβ).deltaPlus () .cont .stop := by
  rw [voiButton2_pos_iff _ (twoState_A1 ε α β c h hε hα hβ) () o₀ .cont .stop]
  constructor
  · intro H
    push Not at H
    obtain ⟨H1, H2⟩ := H
    by_cases hm : (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop ≤ 0
    · have hp : (twoState ε α β c h hε hα hβ).deltaPlus () .cont .stop < 0 := H1 (by linarith)
      rcases lt_or_eq_of_le hm with hm' | hm'
      · exact absurd (beta_lt_alpha_of_inverted ε α β c h hε hα hβ hc hh hm' hp) (not_lt.mpr hαβ)
      · exact absurd (H2 (by rw [hm']; simp)) (not_lt.mpr hp.le)
    · push Not at hm
      refine ⟨hm, ?_⟩
      by_contra hp
      push Not at hp
      exact absurd (H2 (by linarith)) (not_lt.mpr hp)
  · rintro ⟨h1, h2⟩ (⟨H, -⟩ | ⟨-, H⟩) <;> linarith

end TwoStateCoupling

/-! ## T13. The concealment axis -/

section Concealment

/-- Convexity of the parallelogram: a mixture of two garblings of `(α, β)` is a garbling.
Source: none: infrastructure (T13)
Kind: L
Fidelity: n/a -/
theorem inParallelogram_mix {α β α₁ β₁ α₂ β₂ lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (h₁ : InParallelogram α β α₁ β₁) (h₂ : InParallelogram α β α₂ β₂) :
    InParallelogram α β ((1 - lam) * α₁ + lam * α₂) ((1 - lam) * β₁ + lam * β₂) := by
  obtain ⟨p₁, q₁, hp₁, hq₁, e₁, f₁⟩ := h₁
  obtain ⟨p₂, q₂, hp₂, hq₂, e₂, f₂⟩ := h₂
  refine ⟨(1 - lam) * p₁ + lam * p₂, (1 - lam) * q₁ + lam * q₂, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · nlinarith [hlam.1, hlam.2, hp₁.1, hp₂.1]
  · nlinarith [hlam.1, hlam.2, hp₁.2, hp₂.2]
  · nlinarith [hlam.1, hlam.2, hq₁.1, hq₂.1]
  · nlinarith [hlam.1, hlam.2, hq₁.2, hq₂.2]
  · rw [e₁, e₂]; ring
  · rw [f₁, f₂]; ring

/-- The parallelogram contains its own sensor (`p = 1`, `q = 0`). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem inParallelogram_self (α β : ℝ) : InParallelogram α β α β :=
  ⟨1, 0, ⟨zero_le_one, le_rfl⟩, ⟨le_rfl, zero_le_one⟩, by ring, by ring⟩

/-- **The linear concealment family** toward a common value `m`: `α κ = α₀ + κ(m − α₀)`,
`β κ = β₀ + κ(m − β₀)`; at `κ = 1` the sensor is constant `(m, m)` (uninformative).
Source: christiano.md T1 (`β` decreasing in `κ`, `β(1) = α(1)`)
Kind: D
Fidelity: exact (one family of the kind the source describes) -/
def linFamily (x₀ m κ : ℝ) : ℝ := x₀ + κ * (m - x₀)

/-- The linear family stays in `[0, 1]` for `κ ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem linFamily_mem {x₀ m κ : ℝ} (hx : x₀ ∈ Set.Icc (0 : ℝ) 1) (hm : m ∈ Set.Icc (0 : ℝ) 1)
    (hκ : κ ∈ Set.Icc (0 : ℝ) 1) : linFamily x₀ m κ ∈ Set.Icc (0 : ℝ) 1 := by
  unfold linFamily
  constructor <;> nlinarith [hx.1, hx.2, hm.1, hm.2, hκ.1, hκ.2]

/-- **The linear family is a garbling chain**: for `κ ≤ κ'` in `[0, 1]`, the more concealed
sensor is a garbling of the less concealed one (a mixture of it with the constant `(m, m)`).
Source: christiano.md T1 (concealment lowers detection); [[corr-channel-voi-mandate]] T13 ("the linear family toward a common `m` is one")
Kind: P
Fidelity: exact -/
theorem linFamily_chain {α₀ β₀ m κ κ' : ℝ} (hm : m ∈ Set.Icc (0 : ℝ) 1)
    (hκ : κ ∈ Set.Icc (0 : ℝ) 1) (hκ' : κ' ∈ Set.Icc (0 : ℝ) 1) (hle : κ ≤ κ') :
    InParallelogram (linFamily α₀ m κ) (linFamily β₀ m κ) (linFamily α₀ m κ') (linFamily β₀ m κ') := by
  rcases eq_or_lt_of_le hκ.2 with h1 | h1
  · have : κ' = 1 := le_antisymm hκ'.2 (h1 ▸ hle)
    rw [this, ← h1]; exact inParallelogram_self _ _
  · set lam := (κ' - κ) / (1 - κ) with hlam
    have h1κ : 0 < 1 - κ := by linarith
    have hl : lam ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (by linarith) h1κ.le
      · rw [div_le_one h1κ]; linarith [hκ'.2]
    have e : ∀ x₀, linFamily x₀ m κ' = (1 - lam) * linFamily x₀ m κ + lam * m := by
      intro x₀; unfold linFamily; rw [hlam]; field_simp; ring
    rw [e α₀, e β₀]
    exact inParallelogram_mix hl (inParallelogram_self _ _) (inParallelogram_const hm)

variable (ε c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (αf βf : ℝ → ℝ)
  (hαf : ∀ κ, αf κ ∈ Set.Icc (0 : ℝ) 1) (hβf : ∀ κ, βf κ ∈ Set.Icc (0 : ℝ) 1) (τf : ℝ → ℝ)

/-- **`F(κ)`**: the agent's value at concealment level `κ` — the sensor value of `(α κ, β κ)`
minus the transparency cost `τ(κ)`. The two cost readings are the two shapes of `τf`:
(R1) `τf κ = τ(1 − κ)`, (R2) `τf 0 = τ`, `τf κ = 0` for `κ > 0`; the theorems use only the
endpoints `τf 1 = 0`, `τf 0 = τ`, which both readings share.
Source: christiano.md T1 (`F(κ)`); [[corr-wf13-2-inventory]] 2-072
Kind: D
Fidelity: exact (the "delegitimizing to degree `κ`" clause adds nothing to `F` in this model; finding) -/
def concealF (κ : ℝ) : ℝ :=
  sensorValue (twoPoint ε hε) (twoButton (αf κ) (βf κ) (hαf κ) (hβf κ)) (twoValue c h .cont) - τf κ

/-- **T13: the sensor term is antitone** along a garbling chain (T8(a)).
Source: christiano.md T1; [[corr-wf13-2-inventory]] 2-072
Kind: C
Fidelity: exact
Hyps: (a) the chain hypothesis named -/
theorem concealF_sensor_antitone {κ κ' : ℝ} (hchain : InParallelogram (αf κ) (βf κ) (αf κ') (βf κ')) :
    sensorValue (twoPoint ε hε) (twoButton (αf κ') (βf κ') (hαf κ') (hβf κ')) (twoValue c h .cont) ≤
      sensorValue (twoPoint ε hε) (twoButton (αf κ) (βf κ) (hαf κ) (hβf κ)) (twoValue c h .cont) := by
  apply sensorValue_mono
  apply blackwellLE_comap
  exact (blackwellLE_binarySensor_iff (hαf κ) (hβf κ) (hαf κ') (hβf κ')).mpr hchain

/-- A constant sensor `(m, m)` is worth the trivial experiment.
Source: [[corr-channel-voi-mandate]] T13 (`F 1 = sensorValue trivialExp` when `β 1 = α 1`)
Kind: L
Fidelity: exact -/
theorem sensorValue_const_button (m : ℝ) (hm : m ∈ Set.Icc (0 : ℝ) 1) :
    sensorValue (twoPoint ε hε) (twoButton m m hm hm) (twoValue c h .cont) =
      sensorValue (twoPoint ε hε) trivialExp (twoValue c h .cont) := by
  rw [twoState_sensorValue_button, twoState_sensorValue_trivial]
  have e1 : (1 - ε) * m * c - ε * m * h = m * ((1 - ε) * c - ε * h) := by ring
  have e2 : (1 - ε) * (1 - m) * c - ε * (1 - m) * h = (1 - m) * ((1 - ε) * c - ε * h) := by ring
  rw [e1, e2]
  have hm1 : 0 ≤ 1 - m := by linarith [hm.2]
  rcases le_total 0 ((1 - ε) * c - ε * h) with hx | hx
  · rw [max_eq_left (mul_nonneg hm.1 hx), max_eq_left (mul_nonneg hm1 hx), max_eq_left hx]; ring
  · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos hm.1 hx),
      max_eq_right (mul_nonpos_of_nonneg_of_nonpos hm1 hx), max_eq_right hx]; ring

/-- **T13: `F 1 ≥ F 0 ↔ τ ≥ VOI(button₀)`** when the fully concealed sensor is constant
(`β 1 = α 1`) and the cost has endpoints `τf 1 = 0`, `τf 0 = τ` (both readings).
Source: christiano.md T1 ("`F(1) ≥ F(0)` whenever `τ` exceeds the expected value of the information the button would have carried"); [[corr-wf13-2-inventory]] 2-072
Kind: L (`sensorValue_const_button` plus the definition; regraded from P in audit r1)
Fidelity: exact
Hyps: (a) as stated -/
theorem concealF_one_ge_zero_iff (τ : ℝ) (h1 : βf 1 = αf 1) (hτ1 : τf 1 = 0) (hτ0 : τf 0 = τ) :
    concealF ε c h hε αf βf hαf hβf τf 0 ≤ concealF ε c h hε αf βf hαf hβf τf 1 ↔
      voiSensor (twoPoint ε hε) (twoButton (αf 0) (βf 0) (hαf 0) (hβf 0)) (twoValue c h .cont) ≤ τ := by
  unfold concealF
  have e : twoButton (αf 1) (βf 1) (hαf 1) (hβf 1) = twoButton (αf 1) (αf 1) (hαf 1) (hαf 1) := by
    congr 1
  rw [e, sensorValue_const_button ε c h hε (αf 1) (hαf 1), hτ1, hτ0, voiSensor_eq_sub_trivial]
  constructor <;> intro H <;> linarith

/-- **T13, the endpoint difference**: `F 1 − F 0 = τ − VOI(button₀)` exactly, when the fully
concealed sensor is constant (`β 1 = α 1`) and `τf 1 = 0`, `τf 0 = τ`. The one identity behind
both the weak and the strict endpoint comparisons.
Source: christiano.md T1; [[corr-wf13-2-inventory]] 2-072
Kind: L (`sensorValue_const_button` + `voiSensor_eq_sub_trivial` + `ring`)
Fidelity: exact -/
theorem concealF_one_sub_zero (τ : ℝ) (h1 : βf 1 = αf 1) (hτ1 : τf 1 = 0) (hτ0 : τf 0 = τ) :
    concealF ε c h hε αf βf hαf hβf τf 1 - concealF ε c h hε αf βf hαf hβf τf 0 =
      τ - voiSensor (twoPoint ε hε) (twoButton (αf 0) (βf 0) (hαf 0) (hβf 0)) (twoValue c h .cont) := by
  unfold concealF
  have e : twoButton (αf 1) (βf 1) (hαf 1) (hβf 1) = twoButton (αf 1) (αf 1) (hαf 1) (hαf 1) := by
    congr 1
  rw [e, sensorValue_const_button ε c h hε (αf 1) (hαf 1), hτ1, hτ0, voiSensor_eq_sub_trivial]
  ring

/-- **T13, the strict endpoint comparison: `F 0 < F 1 ↔ VOI(button₀) < τ`** — full concealment
is *strictly* preferred to none iff the transparency cost exceeds the button's value of
information. This is what `concealF_not_antitone`'s proof establishes, stated as the theorem
(audit r2 fidelity N3): stronger than `¬ Antitone F` and independent of the domain on which
`F` is read.
Source: christiano.md T1 ("`F(1) ≥ F(0)` whenever `τ` exceeds …", the strict form); [[corr-wf13-2-inventory]] 2-072
Kind: L (`concealF_one_sub_zero` + `linarith`)
Fidelity: exact
Hyps: (a) as stated -/
theorem concealF_zero_lt_one_iff (τ : ℝ) (h1 : βf 1 = αf 1) (hτ1 : τf 1 = 0) (hτ0 : τf 0 = τ) :
    concealF ε c h hε αf βf hαf hβf τf 0 < concealF ε c h hε αf βf hαf hβf τf 1 ↔
      voiSensor (twoPoint ε hε) (twoButton (αf 0) (βf 0) (hαf 0) (hβf 0)) (twoValue c h .cont) < τ := by
  have key := concealF_one_sub_zero ε c h hε αf βf hαf hβf τf τ h1 hτ1 hτ0
  constructor <;> intro H <;> linarith

/-- **T13, the universality claim's finite content**: for every prior, stakes, family and cost
with `τ > VOI(button₀)`, `F` is not antitone — some concealment is preferred to none.
Corollary of the strict endpoint comparison `concealF_zero_lt_one_iff` (`F 0 < F 1` refutes
antitonicity on any domain containing `0` and `1`; `Antitone` here is over all of `ℝ`, the
weaker reading — the strict theorem is the one to cite).
The source's "no assumption on `P` or `V` makes `F` monotone" quantifies over an undefined class;
what is proved is this universality over the parameters (ATTRIBUTION-UNVETTED as a reading).
Source: christiano.md T1 (the conjecture); [[corr-wf13-2-inventory]] 2-072
Kind: L (corollary of `concealF_zero_lt_one_iff`)
Fidelity: variant: universality over `(ε, c, h, α, β, τ)` in place of "no assumption"; weaker than `concealF_zero_lt_one_iff`
Hyps: (a) as stated -/
theorem concealF_not_antitone (τ : ℝ) (h1 : βf 1 = αf 1) (hτ1 : τf 1 = 0) (hτ0 : τf 0 = τ)
    (hgt : voiSensor (twoPoint ε hε) (twoButton (αf 0) (βf 0) (hαf 0) (hβf 0)) (twoValue c h .cont) < τ) :
    ¬ Antitone (concealF ε c h hε αf βf hαf hβf τf) := by
  intro H
  have h10 := H (zero_le_one : (0 : ℝ) ≤ 1)
  have h01 := (concealF_zero_lt_one_iff ε c h hε αf βf hαf hβf τf τ h1 hτ1 hτ0).mpr hgt
  exact absurd h10 (not_le.mpr h01)

end Concealment

/-! ## T14. Holtman C9 -/

section Holtman

/-- **Case A, honest, binding press**: `E[V | a⁰] = v_sh + m − E[X 1_Pr; a⁰]` (the agent stops
when pressed, continues on silence): in product form with `P := E[X 1_Pr; a⁰] = p·x₋` and
`m = E[X]`. **Disclosure (c):** this and the two values below are Holtman's hand-derived
expressions taken as *definitions*, not derived from a `ThreeStep` value; `holtman_on_twoState`
bridges the quantities `P, m, Q` to `−Δ₋, E[X], Δ₊`, and `honestBinding_twoState` shows the
honest side is `v + Δ₊` on `twoState` — which is T10's `forcedValue` (`max(Δ₊, 0)`) only when
`Δ₊ ≥ 0` (the source's Case A assumes the honest agent continues on silence).
Source: holtman.md C9 (Case A, first display)
Kind: D
Fidelity: exact (product form: `p·x₋` is the one number `P`)
Hyps: (c) the value expression is the source's, taken as stated -/
def honestBinding (v m P : ℝ) : ℝ := v + m - P

/-- **Case A, deceptive**: `E[V | a⁻] = v_sh + (1 − q)m − δ` (the agent does not condition on a
press it manufactured; press probability `q`, cost `δ`). **Disclosure (c):** the source's
expression for a *third* agent — beside the correct Bayesian (`sensorValue`) and the imposed-trust
agent (`imposedValue`) — that evaluates silence at the unconditional mean `m`
(`E[X | Pr; a⁻] = E[X | ¬Pr; a⁻] = m`); transcribed, not derived.
Source: holtman.md C9 (Case A, second display)
Kind: D
Fidelity: exact
Hyps: (c) the value expression is the source's, taken as stated -/
def deceptiveBinding (v m q δ : ℝ) : ℝ := v + (1 - q) * m - δ

/-- **Case A's honest value on `twoState` is `v + Δ₊`**: with `m = E[X] = (1−ε)c − εh` and
`P = E[X 1_Pr] = −Δ₋`, `honestBinding v m P = v + Δ₊` — the honest binding agent's value is the
silence cell's expectation, whatever its sign (it continues on silence by fiat; the Bayesian's
`forcedValue = max(Δ₊, 0)` agrees iff `Δ₊ ≥ 0`).
Source: holtman.md C9 (Case A) read on `twoState`; [[corr-channel-voi-audit-r1-adversarial]] N2
Kind: L
Fidelity: exact -/
theorem honestBinding_twoState (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (v : ℝ) :
    honestBinding v ((1 - ε) * c - ε * h) (-(twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop) =
      v + (twoState ε α β c h hε hα hβ).deltaPlus () .cont .stop := by
  rw [twoState_deltaMinus, twoState_deltaPlus]; unfold honestBinding; ring

/-- **T14 (A): deception pays iff `qm + δ < E[X 1_Pr; a⁰]`.**
Source: holtman.md C9 ("deception pays iff `p x₋ > q m + δ`")
Kind: L
Fidelity: exact -/
theorem deception_pays_iff (v m P q δ : ℝ) :
    honestBinding v m P < deceptiveBinding v m q δ ↔ q * m + δ < P := by
  unfold honestBinding deceptiveBinding
  constructor <;> intro H <;> linarith

/-- **T14 (A), the necessary direction**: if deception pays (with `q, m, δ ≥ 0`) then the
below-threshold inequality fails, `0 < E[X 1_Pr; a⁰]`.
Source: holtman.md C9 ("a *necessary* condition for the manipulation incentive is that the below-threshold inequality fails")
Kind: L
Fidelity: exact -/
theorem pos_of_deception_pays (v m P q δ : ℝ) (hq : 0 ≤ q) (hm : 0 ≤ m) (hδ : 0 ≤ δ)
    (H : honestBinding v m P < deceptiveBinding v m q δ) : 0 < P := by
  rw [deception_pays_iff] at H
  nlinarith

/-- **T14 (A): the below-threshold inequality makes honesty dominate for all `q, δ ≥ 0`**
(`m ≥ 0`).
Source: holtman.md C9 ("whenever Total Trust holds (`x₋ ≤ 0`) the honest action dominates")
Kind: L
Fidelity: exact -/
theorem honest_dominates_of_nonpos (v m P q δ : ℝ) (hP : P ≤ 0) (hq : 0 ≤ q) (hm : 0 ≤ m)
    (hδ : 0 ≤ δ) : deceptiveBinding v m q δ ≤ honestBinding v m P := by
  unfold honestBinding deceptiveBinding
  nlinarith

/-- **T14 (A), the iff over the family**: honesty dominates for *every* `q ∈ [0, 1]` and `δ ≥ 0`
iff the below-threshold inequality holds (`m ≥ 0`). For *fixed* `(q, δ)` only the necessary
direction holds (`Witnesses.w_holtman_fixed_fails`): the inventory's "non-interference iff the
thesis's inequality" is the necessary direction plus the limit `q, δ → 0` — finding.
Source: holtman.md C9; [[corr-wf13-inventory]] 018
Kind: L (linear arithmetic; the forward direction is the instance `q = δ = 0`; regraded from P in audit r1)
Fidelity: exact (the universal form; the source's "iff" needs it)
Hyps: (a) `m ≥ 0`; (c) the value expressions are Holtman's, taken as stated (see `honestBinding`) -/
theorem honest_dominates_forall_iff (v m P : ℝ) (hm : 0 ≤ m) :
    (∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ δ, 0 ≤ δ → deceptiveBinding v m q δ ≤ honestBinding v m P) ↔ P ≤ 0 := by
  constructor
  · intro H
    have := H 0 ⟨le_rfl, zero_le_one⟩ 0 le_rfl
    unfold honestBinding deceptiveBinding at this
    linarith
  · intro hP q hq δ hδ
    exact honest_dominates_of_nonpos v m P q δ hP hq.1 hm hδ

/-- **Case B, honest, advisory press**: the agent stops after a press iff it is posterior-optimal,
so `E[V | a⁰] = v_sh + max(m, E[X 1_¬Pr; a⁰])` (in product form, `(1 − p)x₊ = E[X 1_¬Pr]`).
Source: holtman.md C9 (Case B)
Kind: D
Fidelity: exact
Hyps: (c) the value expression is the source's, taken as stated (see `honestBinding`) -/
def honestAdvisory (v m Q : ℝ) : ℝ := v + max m Q

/-- **Case B, deceptive, advisory press**: `E[V | a₁⁻] = v_sh + m − δ` — the advisory deceiver
continues always (the press it manufactured binds nothing), so its value is the unconditional
mean less the cost of deception; no `q`. **Disclosure (c):** Holtman's display taken as a
definition (see `honestBinding`). Added in repair round 2 (audit r2 adversarial N4): the
package had compared `honestAdvisory` against Case A's `deceptiveBinding`, in which `q` is idle.
Source: holtman.md C9 (Case B, second display)
Kind: D
Fidelity: exact
Hyps: (c) the value expression is the source's, taken as stated -/
def deceptiveAdvisory (v m δ : ℝ) : ℝ := v + m - δ

/-- **T14 (B): with an advisory press honesty dominates** — Holtman's display
`v + m − δ ≤ v + max(m, Q)` for every `δ ≥ 0` (and every `p`, `q`, which do not enter): "D2
holds because D1 is hollow": a button the agent is free to ignore is not worth disabling.
Source: holtman.md C9 (Case B, "Honesty dominates for every `p, q, δ`")
Kind: L
Fidelity: exact (the source's display; restated in repair round 2 from the binding deceiver's value, where `q` was idle)
Hyps: (c) the value expressions are Holtman's, taken as stated -/
theorem honest_advisory_dominates (v m Q δ : ℝ) (hδ : 0 ≤ δ) :
    deceptiveAdvisory v m δ ≤ honestAdvisory v m Q := by
  unfold honestAdvisory deceptiveAdvisory
  linarith [le_max_left m Q]

/-- Case A's binding deceiver at `q = 0` is Case B's advisory deceiver. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem deceptiveBinding_zero (v m δ : ℝ) : deceptiveBinding v m 0 δ = deceptiveAdvisory v m δ := by
  unfold deceptiveBinding deceptiveAdvisory; ring

/-- **T14 (B), against Case A's deceiver**: for `m ≥ 0`, honesty with an advisory press also
dominates the *binding* deceiver's value `v + (1−q)m − δ` at every `q ∈ [0, 1]` — a weaker
statement than the display (the `q > 0` instances are implied by `q = 0`); the package's
round-1 form of Case B, kept as a corollary.
Source: holtman.md C9 (Case B)
Kind: L (corollary of `honest_advisory_dominates` via `deceptiveBinding_zero`)
Fidelity: weaker: compares against Case A's deceiver, `q` idle
Hyps: (a) `m ≥ 0`; (c) as above -/
theorem honest_advisory_dominates_binding (v m Q q δ : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) (hm : 0 ≤ m)
    (hδ : 0 ≤ δ) :
    deceptiveBinding v m q δ ≤ honestAdvisory v m Q := by
  have h := honest_advisory_dominates v m Q δ hδ
  unfold deceptiveAdvisory at h
  unfold deceptiveBinding
  nlinarith [hq.1, hq.2]

/-- **Holtman's quantities on `twoState`**: `P = E[X 1_Pr] = −Δ₋`, `m = E[X] = (1−ε)c − εh`,
`E[X 1_¬Pr] = Δ₊` — so Case A's "deception pays" is `qm + δ < −Δ₋` and its honest-dominance
condition is `0 ≤ Δ₋`, the base-rate inequality (C10).
Source: holtman.md C9–C10 ("one inequality governs desideratum 1 … desideratum 2 …")
Kind: L
Fidelity: exact -/
theorem holtman_on_twoState (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (o : Obs) :
    (twoState ε α β c h hε hα hβ).obsExpect () .press ((twoState ε α β c h hε hα hβ).Xo () o .cont .stop) =
        -(twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop ∧
      expect (twoPoint ε hε) ((twoState ε α β c h hε hα hβ).Xo () o .cont .stop) = (1 - ε) * c - ε * h ∧
      (twoState ε α β c h hε hα hβ).obsExpect () .silent ((twoState ε α β c h hε hα hβ).Xo () o .cont .stop) =
        (twoState ε α β c h hε hα hβ).deltaPlus () .cont .stop := by
  refine ⟨?_, twoState_expect_Xo ε α β c h hε hα hβ o, ?_⟩
  · rw [deltaMinus, neg_neg]; rfl
  · rw [deltaPlus]; rfl

end Holtman

end

end Cleanroom.Corrigibility.CorrChannelVoi
