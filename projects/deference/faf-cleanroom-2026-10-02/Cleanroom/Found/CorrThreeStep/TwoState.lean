import Cleanroom.Found.CorrThreeStep.Identities
import Cleanroom.Found.CorrThreeStep.Thresholds
import Cleanroom.Found.CorrThreeStep.GeneralMenu

/-!
# The two-state instance: the base-rate bracket, `ε*`, Wentworth's bound, the band

On `twoState ε α β c h` (`Ω = {right, wrong}`, `μ(wrong) = ε`, press rates `α` when right and
`β` when wrong, continuing worth `c` when right and `−h` when wrong, stopping worth `0`):

* the closed forms `Δ₋ = εβh − (1 − ε)αc`, `Δ₊ = (1 − ε)(1 − α)c − ε(1 − β)h`,
  `P(Pr) = (1 − ε)α + εβ`, `E_μ[X] = (1 − ε)c − εh`, the posterior `P(wrong | Pr)`;
* **T3 (F3)**: `Δ₋ ≥ 0 ↔ (1 − ε)αc ≤ εβh ↔ α/β ≤ (ε/(1 − ε))·(h/c) ↔ c/(c + h) ≤ P(wrong | Pr)`
  (each odds form under the positivity it needs; the last through T5 on the posterior, which is
  `posteriorPress`'s weight — not a second posterior); the silence half
  `Δ₊ ≥ 0 ↔ (ε/(1 − ε))·(h/c) ≤ (1 − α)/(1 − β)`; and K1 ∧ K2 ⟹ `α ≤ β`;
* **T7**: `Δ₋ ≥ 0 ↔ ε* ≤ ε` with `ε* = αc/(αc + βh) = r/(1 + r)`, `r = (α/β)(c/h)`; in the regime
  `0 < VOI ↔ ε* < ε` — D1 (strict) and the repair incentive vanish at the same `ε`;
* **T8**: Wentworth's regime lemma, his signed "VOI" `= Δ₋`, the bound `Δ₋ ≤ εβh ≤ εh`;
* **T9(d)**: invariance under `(c, h) ↦ (λc, λh)` and the band
  `((1 − ε)/ε)(α/β) < h/c < (1 − ε)/ε ↔ 0 < Δ₋ ∧ 0 < E_μ[X]`;
* **T12 (stretch)**: `ε*(ε/2, β, c, h) < ε` whenever `c < 2βh`.
* **T10 on `twoState`** (repair round 2): Prop. 9.2's sign split is T3's first form
  (`twoState_sign_split_is_T3`).
* **T14's world-mass form** (repair round 2): the perfect-information bound
  `VOI₂ ≤ min((1 − ε)c, εh) ≤ min(ε, 1 − ε) · max(c, h)`, no regime.

Everything is `L` or `C` except `twoState_alpha_le_beta_of_both` (`P`, small). Sources:
`filler.md` F3; `mm.md` I13.3–I13.4; position statement §2.13; `wentworth.md` §2.4;
`channel-final.md` D13, P10; `miri.md` Prop. 9.2.
-/

namespace Cleanroom.Found.CorrThreeStep

open FactoredSpaces Finset ThreeStep

section TwoStateForms

variable (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-! ## Closed forms -/

/-- A1 holds on the two-state instance by construction.
Source: [[corr-wf13-inventory]] 003 / miri.md Dict-6 ("A1 holds")
Kind: L
Fidelity: exact -/
lemma twoState_A1 : (twoState ε α β c h hε hα hβ).A1 := fun _ _ _ _ _ => rfl

/-- `Δ₋ = εβh − (1 − ε)αc` on the two-state instance.
Source: [[corr-wf14-inventory]] 004 / filler.md F3
Kind: L
Fidelity: exact -/
lemma twoState_deltaMinus :
    (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop = ε * β * h - (1 - ε) * α * c := by
  simp only [deltaMinus, obsExpect, obsWeight_press, World.sum_eq, twoState, twoPoint_right,
    twoPoint_wrong, twoPress, twoValue, Xo]
  ring

/-- `Δ₊ = (1 − ε)(1 − α)c − ε(1 − β)h` on the two-state instance.
Source: [[corr-wf14-inventory]] 004 / filler.md F3; mm.md I13.4
Kind: L
Fidelity: exact -/
lemma twoState_deltaPlus :
    (twoState ε α β c h hε hα hβ).deltaPlus () .cont .stop =
      (1 - ε) * (1 - α) * c - ε * (1 - β) * h := by
  simp only [deltaPlus, obsExpect, obsWeight_silent, World.sum_eq, twoState, twoPoint_right,
    twoPoint_wrong, twoPress, twoValue, Xo]
  ring

/-- `P(Pr) = (1 − ε)α + εβ` on the two-state instance.
Source: [[corr-wf13-inventory]] 003 / miri.md Dict-6
Kind: L
Fidelity: exact -/
lemma twoState_pressMass : (twoState ε α β c h hε hα hβ).pressMass () = (1 - ε) * α + ε * β := by
  simp only [pressMass, World.sum_eq, twoState, twoPoint_right, twoPoint_wrong, twoPress]

/-- `E_μ[X] = (1 − ε)c − εh` on the two-state instance (any observation index: A1).
Source: [[corr-wf13-2-inventory]] 066 / wentworth.md §2.4 (the no-signal decision)
Kind: L
Fidelity: exact -/
lemma twoState_expect_Xo (o : Obs) :
    expect (twoPoint ε hε) ((twoState ε α β c h hε hα hβ).Xo () o .cont .stop) = (1 - ε) * c - ε * h := by
  simp only [expect, World.sum_eq, twoState, twoPoint_right, twoPoint_wrong, twoValue, Xo]
  ring

/-- The two-state posterior `P(wrong | Pr) = εβ / ((1 − ε)α + εβ)` is `posteriorPress`'s weight.
Source: [[corr-wf14-inventory]] 004 / filler.md F3; position statement §2.13(b)
Kind: L
Fidelity: exact -/
lemma twoState_posteriorPress_wrong :
    (twoState ε α β c h hε hα hβ).posteriorPress () .wrong = ε * β / ((1 - ε) * α + ε * β) := by
  rw [posteriorPress, twoState_pressMass]
  simp only [twoState, twoPoint_wrong, twoPress]

/-- Under `0 < P(Pr)`, `P(right | Pr) = 1 − P(wrong | Pr)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma twoState_posteriorPress_right (hpm : 0 < (1 - ε) * α + ε * β) :
    (twoState ε α β c h hε hα hβ).posteriorPress () .right =
      1 - (twoState ε α β c h hε hα hβ).posteriorPress () .wrong := by
  rw [posteriorPress, posteriorPress, twoState_pressMass]
  simp only [twoState, twoPoint_right, twoPoint_wrong, twoPress]
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hpm.ne']

/-- `E_P[X | Pr] = q·(−h) + (1 − q)·c` with `q = P(wrong | Pr)`, under `0 < P(Pr)`: the
conditional form is the compliance-threshold shape with the posterior as its weight.
Source: [[corr-wf13-inventory]] 002 / position statement §2.13(a); miri.md I12.1
Kind: L
Fidelity: exact -/
lemma twoState_condExpPress_Xo (hpm : 0 < (1 - ε) * α + ε * β) :
    (twoState ε α β c h hε hα hβ).condExpPress () ((twoState ε α β c h hε hα hβ).Xo () .press .cont .stop) =
      (twoState ε α β c h hε hα hβ).posteriorPress () .wrong * (-h) +
        (1 - (twoState ε α β c h hε hα hβ).posteriorPress () .wrong) * c := by
  rw [condExpPress_eq_sum_posterior, World.sum_eq, ← twoState_posteriorPress_right ε α β c h hε hα hβ hpm]
  simp only [twoState, twoValue, Xo]
  ring

/-! ## T3 — F3: the two-state instance is the base-rate bracket -/

/-- **F3, first form.** `Δ₋ ≥ 0 ↔ (1 − ε)αc ≤ εβh`.
Source: [[corr-wf14-inventory]] 004 / filler.md F3; miri.md Prop. 9.2 (C2 clause)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoState_deltaMinus_nonneg_iff :
    0 ≤ (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop ↔ (1 - ε) * α * c ≤ ε * β * h := by
  rw [twoState_deltaMinus]
  constructor <;> intro H <;> linarith

/-- **F3, strict first form.** `Δ₋ > 0 ↔ (1 − ε)αc < εβh`.
Source: [[corr-wf14-inventory]] 004 / filler.md F3
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoState_deltaMinus_pos_iff :
    0 < (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop ↔ (1 - ε) * α * c < ε * β * h := by
  rw [twoState_deltaMinus]
  constructor <;> intro H <;> linarith

/-- **F3, odds form.** Under `ε < 1`, `0 < β`, `0 < c`: `Δ₋ ≥ 0 ↔ α/β ≤ (ε/(1 − ε))·(h/c)` —
position statement §2.13(b) with "≲" sharpened to "≤". The odds are meaningless at `β = 0` or
`ε = 1`; the hypotheses are what keep Lean's `x/0 = 0` out.
Source: [[corr-wf14-inventory]] 004 / filler.md F3; [[corr-wf13-inventory]] 003 / miri.md I13.1; position statement §2.13(b)
Kind: L
Fidelity: exact (finding: the source's "≲" is "≤")
Hyps: (a) the positivity hypotheses are exactly where the odds forms are defined -/
theorem twoState_deltaMinus_nonneg_iff_odds (hε1 : ε < 1) (hβ0 : 0 < β) (hc : 0 < c) :
    0 ≤ (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop ↔
      α / β ≤ ε / (1 - ε) * (h / c) := by
  rw [twoState_deltaMinus_nonneg_iff, div_mul_div_comm,
    div_le_div_iff₀ hβ0 (mul_pos (sub_pos.mpr hε1) hc)]
  constructor <;> intro H <;> linarith

/-- **F3, strict odds form.** Under the same positivity, `Δ₋ > 0 ↔ α/β < (ε/(1 − ε))·(h/c)`.
Source: [[corr-wf13-2-inventory]] 066 / wentworth.md §2.4(a)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoState_deltaMinus_pos_iff_odds (hε1 : ε < 1) (hβ0 : 0 < β) (hc : 0 < c) :
    0 < (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop ↔
      α / β < ε / (1 - ε) * (h / c) := by
  rw [twoState_deltaMinus_pos_iff, div_mul_div_comm,
    div_lt_div_iff₀ hβ0 (mul_pos (sub_pos.mpr hε1) hc)]
  constructor <;> intro H <;> linarith

/-- **F3, posterior form.** Under `0 < P(Pr)` and `0 < c + h`: `Δ₋ ≥ 0 ↔ c/(c + h) ≤ P(wrong | Pr)`,
proved through the conditional form and T5 on `posteriorPress` — the posterior is
`condExpPress`'s weight, not a second definition.
Source: [[corr-wf14-inventory]] 004 / filler.md F3; [[corr-wf13-inventory]] 002 / miri.md I12.1
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoState_deltaMinus_nonneg_iff_threshold (hpm : 0 < (1 - ε) * α + ε * β) (hch : 0 < c + h) :
    0 ≤ (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop ↔
      complianceThreshold c h ≤ (twoState ε α β c h hε hα hβ).posteriorPress () .wrong := by
  have hpm' : 0 < (twoState ε α β c h hε hα hβ).pressMass () := by rw [twoState_pressMass]; exact hpm
  rw [deltaMinus, neg_nonneg, ← belowThresholdIneq, belowThresholdIneq_iff_condExpPress _ _ _ hpm',
    twoState_condExpPress_Xo ε α β c h hε hα hβ hpm, complianceThreshold_iff _ _ _ hch]

/-- **F3, explicit posterior form.** `Δ₋ ≥ 0 ↔ c/(c + h) ≤ εβ/(εβ + (1 − ε)α)`.
Source: [[corr-wf14-inventory]] 004 / filler.md F3; position statement §2.13(b)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoState_deltaMinus_nonneg_iff_posterior (hpm : 0 < (1 - ε) * α + ε * β) (hch : 0 < c + h) :
    0 ≤ (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop ↔
      c / (c + h) ≤ ε * β / (ε * β + (1 - ε) * α) := by
  rw [twoState_deltaMinus_nonneg_iff_threshold ε α β c h hε hα hβ hpm hch,
    twoState_posteriorPress_wrong, complianceThreshold, add_comm ((1 - ε) * α)]

/-- **F3, silence half.** Under `ε < 1`, `β < 1`, `0 < c`: `Δ₊ ≥ 0 ↔ (ε/(1 − ε))·(h/c) ≤ (1 − α)/(1 − β)`
— `mm.md` I13.4's addition, absent from §2.13(b).
Source: [[corr-wf14-inventory]] 004 / filler.md F3; [[corr-wf13-inventory]] 003 / mm.md I13.4
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoState_deltaPlus_nonneg_iff_odds (hε1 : ε < 1) (hβ1 : β < 1) (hc : 0 < c) :
    0 ≤ (twoState ε α β c h hε hα hβ).deltaPlus () .cont .stop ↔
      ε / (1 - ε) * (h / c) ≤ (1 - α) / (1 - β) := by
  rw [twoState_deltaPlus, div_mul_div_comm,
    div_le_div_iff₀ (mul_pos (sub_pos.mpr hε1) hc) (sub_pos.mpr hβ1)]
  constructor <;> intro H <;> linarith

/-- **K1 ∧ K2 ⟹ K3.** Under `0 < ε < 1`, `0 < c`, `0 < h`: both halves (`Δ₋ ≥ 0` and `Δ₊ ≥ 0`)
force `α ≤ β` — a monotone sensor is a theorem under Value on the two-option menu.
Source: [[corr-wf14-inventory]] 004 / filler.md F3; detection.md K1–K3; mm.md I13.4 (the flag)
Kind: P
Fidelity: stronger: holds on the closed intervals `α, β ∈ [0, 1]` (K3 states it on `(0, 1)`)
Hyps: (a) only -/
theorem twoState_alpha_le_beta_of_both (hε0 : 0 < ε) (hε1 : ε < 1) (hc : 0 < c) (hh : 0 < h)
    (h1 : 0 ≤ (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop)
    (h2 : 0 ≤ (twoState ε α β c h hε hα hβ).deltaPlus () .cont .stop) : α ≤ β := by
  rw [twoState_deltaMinus_nonneg_iff] at h1
  rw [twoState_deltaPlus] at h2
  have h2' : ε * (1 - β) * h ≤ (1 - ε) * (1 - α) * c := by linarith
  have hK : 0 < (1 - ε) * ε * c * h := by
    have := sub_pos.mpr hε1
    positivity
  have hprod := mul_le_mul h1 h2' (mul_nonneg (mul_nonneg hε0.le (sub_nonneg.mpr hβ.2)) hh.le)
    (mul_nonneg (mul_nonneg hε0.le hβ.1) hh.le)
  have e1 : (1 - ε) * α * c * (ε * (1 - β) * h) = (1 - ε) * ε * c * h * (α * (1 - β)) := by ring
  have e2 : ε * β * h * ((1 - ε) * (1 - α) * c) = (1 - ε) * ε * c * h * (β * (1 - α)) := by ring
  rw [e1, e2] at hprod
  have := le_of_mul_le_mul_left hprod hK
  linarith

/-! ## T7 — `ε*` and the D1/VOI coupling -/

/-- **T7.** Under `0 < αc + βh` (the junk-value guard): `Δ₋ ≥ 0 ↔ ε* ≤ ε`.
Source: [[corr-wf13-inventory]] 004; [[corr-wf14b-inventory]] 033 / channel-final.md P10, D13
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoState_deltaMinus_nonneg_iff_epsStar (hpos : 0 < α * c + β * h) :
    0 ≤ (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop ↔ epsStar α β c h ≤ ε := by
  rw [twoState_deltaMinus_nonneg_iff, epsStar, div_le_iff₀ hpos]
  constructor <;> intro H <;> linarith

/-- **T7, strict.** `Δ₋ > 0 ↔ ε* < ε`.
Source: [[corr-wf14b-inventory]] 033 / channel-final.md D13
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoState_deltaMinus_pos_iff_epsStar (hpos : 0 < α * c + β * h) :
    0 < (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop ↔ epsStar α β c h < ε := by
  rw [twoState_deltaMinus_pos_iff, epsStar, div_lt_iff₀ hpos]
  constructor <;> intro H <;> linarith

/-- **T7, the ratio form.** `ε* = r/(1 + r)` with `r = (α/β)(c/h)`, for `0 < β`, `0 < h`,
`0 ≤ α`, `0 ≤ c`.
Source: [[corr-wf14b-inventory]] 033 / channel-final.md D13
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem epsStar_eq_ratio (hα0 : 0 ≤ α) (hc : 0 ≤ c) (hβ0 : 0 < β) (hh : 0 < h) :
    epsStar α β c h = (α / β * (c / h)) / (1 + α / β * (c / h)) := by
  unfold epsStar
  have hβh : 0 < β * h := mul_pos hβ0 hh
  have hden : 0 < α * c + β * h := add_pos_of_nonneg_of_pos (mul_nonneg hα0 hc) hβh
  rw [div_mul_div_comm, one_add_div hβh.ne', div_div_div_cancel_right₀ hβh.ne', add_comm]

/-- **T7, the coupling.** In the continue-by-default regime, the two-option value of the button
is positive iff `ε* < ε`: desideratum 1 (strictly) and the repair incentive stand or fall
together (Prop. 10.5's finite half).
Source: [[corr-wf13-inventory]] 004 / miri.md Prop. 10.5; harms.md item 20; hudson.md I12–I13
Kind: C
Fidelity: variant: the continue-by-default regime in place of Prop. 10.5's monotone-sensor hypothesis `β ≥ α`; where both apply they agree (under both strict halves `α ≤ β` follows, `twoState_alpha_le_beta_of_both`)
Hyps: (a) A1 holds on `twoState` by construction; the regime and `0 < αc + βh` are named -/
theorem twoState_voiButton2_pos_iff_epsStar (o₀ : Obs) (hpos : 0 < α * c + β * h)
    (hprior : 0 ≤ expect (twoPoint ε hε) ((twoState ε α β c h hε hα hβ).Xo () o₀ .cont .stop))
    (hsilent : 0 ≤ (twoState ε α β c h hε hα hβ).deltaPlus () .cont .stop) :
    0 < (twoState ε α β c h hε hα hβ).voiButton2 () o₀ .cont .stop ↔ epsStar α β c h < ε := by
  rw [voiButton2_eq_max_deltaMinus _ (twoState_A1 ε α β c h hε hα hβ) () o₀ .cont .stop hprior hsilent,
    ← twoState_deltaMinus_pos_iff_epsStar ε α β c h hε hα hβ hpos]
  constructor
  · intro H
    rcases lt_max_iff.mp H with H | H
    · exact H
    · exact absurd H (lt_irrefl 0)
  · intro H
    exact lt_max_of_lt_left H

/-! ## T8 — Wentworth's closed form and the bound `εβh` -/

/-- **T8(i), the regime lemma.** `ε ≤ c/(c + h)` and `α ≤ β` put the two-state instance in the
continue-by-default regime: `E_μ[X] ≥ 0` and `Δ₊ ≥ 0` (Wentworth's justification that continuing
on silence is right).
Source: [[corr-wf13-2-inventory]] 066 / wentworth.md §2.4 (set-up)
Kind: C (two monotone multiplications and `linarith` on the closed forms; relabelled from P in repair round 2)
Fidelity: stronger: Wentworth's strict `ε < c/(c + h)` weakened to `≤`
Hyps: (a) only -/
theorem twoState_regime_of_threshold (hc : 0 < c) (hh : 0 < h) (hεth : ε ≤ complianceThreshold c h)
    (hαβ : α ≤ β) (o₀ : Obs) :
    0 ≤ expect (twoPoint ε hε) ((twoState ε α β c h hε hα hβ).Xo () o₀ .cont .stop) ∧
      0 ≤ (twoState ε α β c h hε hα hβ).deltaPlus () .cont .stop := by
  rw [twoState_expect_Xo, twoState_deltaPlus]
  have h1 : ε * h ≤ (1 - ε) * c := by
    unfold complianceThreshold at hεth
    rw [le_div_iff₀ (by linarith)] at hεth
    linarith
  refine ⟨by linarith, ?_⟩
  have h2 : (1 - β) * (ε * h) ≤ (1 - β) * ((1 - ε) * c) :=
    mul_le_mul_of_nonneg_left h1 (by linarith [hβ.2])
  have h3 : (1 - β) * ((1 - ε) * c) ≤ (1 - α) * ((1 - ε) * c) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (by linarith [hε.2]) hc.le)
  linarith

/-- The expected loss of "stop on press, continue on silence":
`P(press, right)·c + P(silent, wrong)·h = (1 − ε)αc + ε(1 − β)h`.
Source: [[corr-wf13-2-inventory]] 066 / wentworth.md §2.4
Kind: D
Fidelity: exact -/
noncomputable def stopOnPressLoss (ε α β c h : ℝ) : ℝ := (1 - ε) * α * c + ε * (1 - β) * h

/-- The expected loss of continuing without the signal: `εh`.
Source: [[corr-wf13-2-inventory]] 066 / wentworth.md §2.4
Kind: D
Fidelity: exact -/
noncomputable def noSignalLoss (ε h : ℝ) : ℝ := ε * h

/-- **T8(ii).** Wentworth's "VOI" — the no-signal loss minus the stop-on-press loss — is exactly
`Δ₋`, the *signed* policy difference. The value of information proper is its positive part
(`voiButton2_eq_max_deltaMinus`); his quantity can be negative.
Source: [[corr-wf13-2-inventory]] 066 / wentworth.md §2.4 (`VOI = εβh − (1 − ε)αc`)
Kind: L
Fidelity: exact (finding: the source's "VOI" is signed)
Hyps: (a) only -/
theorem wentworth_voi_eq_deltaMinus :
    noSignalLoss ε h - stopOnPressLoss ε α β c h = (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop := by
  rw [twoState_deltaMinus, noSignalLoss, stopOnPressLoss]
  ring

/-- **T8(iii), first bound.** `Δ₋ ≤ εβh` (for `0 ≤ c`).
Source: [[corr-wf13-2-inventory]] 066 / wentworth.md §2.4(b)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoState_deltaMinus_le (hc : 0 ≤ c) :
    (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop ≤ ε * β * h := by
  rw [twoState_deltaMinus]
  have := mul_nonneg (mul_nonneg (sub_nonneg.mpr hε.2) hα.1) hc
  linarith

/-- **T8(iii), second bound.** `εβh ≤ εh` (for `0 ≤ ε`, `β ≤ 1`, `0 ≤ h`).
Source: [[corr-wf13-2-inventory]] 066 / wentworth.md §2.4(b)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem eps_beta_h_le (hε0 : 0 ≤ ε) (hβ1 : β ≤ 1) (hh : 0 ≤ h) : ε * β * h ≤ ε * h := by
  have := mul_nonneg (mul_nonneg hε0 (sub_nonneg.mpr hβ1)) hh
  linarith

/-- **T8(iii), the repair incentive is `O(ε)`.** In the regime, the two-option value of the
button is at most `εβh ≤ εh`.
Source: [[corr-wf13-2-inventory]] 066 / wentworth.md §2.4(b)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoState_voiButton2_le (o₀ : Obs) (hc : 0 ≤ c) (hh : 0 ≤ h)
    (hprior : 0 ≤ expect (twoPoint ε hε) ((twoState ε α β c h hε hα hβ).Xo () o₀ .cont .stop))
    (hsilent : 0 ≤ (twoState ε α β c h hε hα hβ).deltaPlus () .cont .stop) :
    (twoState ε α β c h hε hα hβ).voiButton2 () o₀ .cont .stop ≤ ε * h := by
  rw [voiButton2_eq_max_deltaMinus _ (twoState_A1 ε α β c h hε hα hβ) () o₀ .cont .stop hprior hsilent]
  exact max_le ((twoState_deltaMinus_le ε α β c h hε hα hβ hc).trans
    (eps_beta_h_le ε β h hε.1 hβ.2 hh)) (mul_nonneg hε.1 hh)

/-- **The signal-mass bound on the two-state instance** (no regime): `VOI₂ ≤ min(P(Pr), P(¬Pr)) ·
max(c, h)` with `P(Pr) = (1 − ε)α + εβ`. Incomparable with Wentworth's world-mass bound `εh`
(`twoState_voiButton2_le`): at the `h = 10` regime instance it reads `161/400 ≤ 37/40` against
`161/400 ≤ 1/2`, and with a sensor that presses rarely it is the tighter of the two.
Source: [[corr-three-step-mandate]] T14; wentworth.md §2.4(b)
Kind: L
Fidelity: variant: minority signal mass, see `voiButton2_le_minority_mass_mul`
Hyps: (a) only -/
theorem twoState_voiButton2_le_minority (o₀ : Obs) (hc : 0 ≤ c) (hh : 0 ≤ h) :
    (twoState ε α β c h hε hα hβ).voiButton2 () o₀ .cont .stop ≤
      min ((1 - ε) * α + ε * β) (1 - ((1 - ε) * α + ε * β)) * max c h := by
  have := (twoState ε α β c h hε hα hβ).voiButton2_le_minority_mass_mul
    (twoState_A1 ε α β c h hε hα hβ) () o₀ .cont .stop (M := max c h) fun ω => by
      cases ω <;> simp [twoState, Xo, twoValue, abs_of_nonneg hc, abs_of_nonneg hh]
  rwa [twoState_pressMass] at this

/-- On `twoState` the value with the world revealed is `(1 − ε)c` for `c, h ≥ 0` (continue when
right, stop when wrong).
Source: [[corr-wf13-2-inventory]] 066 / wentworth.md §2.4(b) (set-up)
Kind: L
Fidelity: exact -/
lemma twoState_perfect_value (hc : 0 ≤ c) (hh : 0 ≤ h) (o₀ : Obs) :
    expect ((twoState ε α β c h hε hα hβ).μ ())
        (fun ω => max ((twoState ε α β c h hε hα hβ).V () o₀ .cont ω)
          ((twoState ε α β c h hε hα hβ).V () o₀ .stop ω)) = (1 - ε) * c := by
  simp only [expect, World.sum_eq, twoState, twoPoint_right, twoPoint_wrong, twoValue]
  rw [max_eq_left hc, max_eq_right (by linarith : -h ≤ 0)]
  ring

/-- On `twoState` the two-option prior value is `max((1 − ε)c − εh, 0)`.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(b) (the prior maximum on `{cont, stop}`)
Kind: L
Fidelity: exact -/
lemma twoState_twoOptionPriorValue (o₀ : Obs) :
    (twoState ε α β c h hε hα hβ).twoOptionPriorValue () o₀ .cont .stop =
      max ((1 - ε) * c - ε * h) 0 := by
  have hVc : expect (twoPoint ε hε) (twoValue c h .cont) = (1 - ε) * c - ε * h := by
    simp only [expect, World.sum_eq, twoPoint_right, twoPoint_wrong, twoValue]; ring
  have hVs : expect (twoPoint ε hε) (twoValue c h .stop) = 0 := by
    simp only [expect, World.sum_eq, twoPoint_right, twoPoint_wrong, twoValue]; ring
  show max (expect (twoPoint ε hε) (twoValue c h .cont)) (expect (twoPoint ε hε) (twoValue c h .stop)) = _
  rw [hVc, hVs]

/-- **The perfect-information bound on `twoState`, no regime**: `VOI₂ ≤ min((1 − ε)c, εh)` for
`c, h ≥ 0` — Wentworth's `εh` bound (T8(iii), in the regime) extended off the regime, and the
"minority-state probability × maximal loss" remark in its own terms: `εh` is the wrong-world mass
times the harm, `(1 − ε)c` the right-world mass times the forgone gain. Via `voiButton2_le_vopi`
with `VOPI = (1 − ε)c − max((1 − ε)c − εh, 0) = min((1 − ε)c, εh)`.
Source: [[corr-three-step-mandate]] T14; wentworth.md §2.4(b)
Kind: C (`voiButton2_le_vopi` + the two closed forms + one sign split)
Fidelity: exact (the remark's general form on the two-state instance)
Hyps: (a) only -/
theorem twoState_voiButton2_le_perfectInfo (hc : 0 ≤ c) (hh : 0 ≤ h) (o₀ : Obs) :
    (twoState ε α β c h hε hα hβ).voiButton2 () o₀ .cont .stop ≤ min ((1 - ε) * c) (ε * h) := by
  have hperf := (twoState ε α β c h hε hα hβ).voiButton2_le_vopi
    (twoState_A1 ε α β c h hε hα hβ) () o₀ .cont .stop
  rw [twoState_perfect_value ε α β c h hε hα hβ hc hh o₀,
    twoState_twoOptionPriorValue ε α β c h hε hα hβ o₀] at hperf
  refine hperf.trans ?_
  rcases le_total 0 ((1 - ε) * c - ε * h) with h0 | h0
  · rw [max_eq_left h0]; exact le_min (by linarith) (by linarith)
  · rw [max_eq_right h0]; exact le_min (by linarith) (by linarith)

/-- **The mandate's T14 bound in its literal world-mass form**, no regime: on `twoState` with
`c, h ≥ 0`, `VOI₂ ≤ min(ε, 1 − ε) · max(c, h)` — the minority *world* mass times the maximal
stake. From `twoState_voiButton2_le_perfectInfo`; compare the signal-mass form
`twoState_voiButton2_le_minority`, which is incomparable with it.
Source: [[corr-three-step-mandate]] T14 ("any binary signal is worth at most minority-probability × maximal loss"); wentworth.md §2.4(b)
Kind: L
Fidelity: exact (the mandate's phrase, verbatim, on the two-state instance)
Hyps: (a) only -/
theorem twoState_voiButton2_le_world_mass (hc : 0 ≤ c) (hh : 0 ≤ h) (o₀ : Obs) :
    (twoState ε α β c h hε hα hβ).voiButton2 () o₀ .cont .stop ≤ min ε (1 - ε) * max c h := by
  refine (twoState_voiButton2_le_perfectInfo ε α β c h hε hα hβ hc hh o₀).trans ?_
  have hε0 := hε.1
  have hε1 := hε.2
  rcases le_total ε (1 - ε) with hm | hm
  · rw [min_eq_left hm]
    exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_left (le_max_right c h) hε0)
  · rw [min_eq_right hm]
    exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left (le_max_left c h) (by linarith))

/-! ## T10 on `twoState` — Prop. 9.2's sign split is T3's first form -/

/-- **T10 on `twoState` is T3's first form.** With `0 < c`, `0 < h` the sign split of Prop. 9.2
puts `right` in `Ω⁺` and `wrong` in `Ω⁻`, and the below-threshold inequality on `X_Pr` reads
`(1 − ε)αc ≤ εβh` — the mandate's T10 clause, instantiated (the ledger's Witness cell for
`belowThresholdIneq_iff_sign_split` asserted this without a declaration; adopted from the round-2
fidelity audit's probe 2).
Source: [[corr-wf13-inventory]] 011 / miri.md Prop. 9.2 (on C2); filler.md F3
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoState_sign_split_is_T3 (hc : 0 < c) (hh : 0 < h) :
    ((twoState ε α β c h hε hα hβ).belowThresholdIneq ()
        ((twoState ε α β c h hε hα hβ).Xo () .press .cont .stop)) ↔
      (1 - ε) * α * c ≤ ε * β * h := by
  rw [belowThresholdIneq_iff_sign_split]
  simp only [sum_filter, World.sum_eq, twoState, twoPoint_right, twoPoint_wrong, twoPress,
    twoValue, Xo]
  have hnh : ¬ (0 < -h - 0) := by linarith
  have hnc : ¬ (c - 0 ≤ 0) := by linarith
  have hc' : 0 < c - 0 := by linarith
  have hh' : -h - 0 ≤ 0 := by linarith
  rw [if_pos hc', if_neg hnh, if_neg hnc, if_pos hh', abs_of_nonpos hh']
  constructor <;> intro H <;> linarith

/-! ## T9(d) — scaling invariance and the band -/

/-- `Δ₋` is homogeneous of degree one in the stakes `(c, h)`.
Source: [[corr-wf14b-inventory]] 005 / general-object-final.md D10 (stakes)
Kind: L
Fidelity: exact -/
theorem twoState_deltaMinus_scale (l : ℝ) :
    (twoState ε α β (l * c) (l * h) hε hα hβ).deltaMinus () .cont .stop =
      l * (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop := by
  rw [twoState_deltaMinus, twoState_deltaMinus]
  ring

/-- **T9(d), invariance.** The sign of `Δ₋` is invariant under `(c, h) ↦ (λc, λh)`, `λ > 0`.
Source: [[corr-wf14b-inventory]] 005(d) / legitimacy-general-final.md Statement 4(d) ("homogeneous of degree zero in the stakes", check X2); general-object-final.md D10 (the stakes)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoState_deltaMinus_nonneg_scale_iff (l : ℝ) (hl : 0 < l) :
    0 ≤ (twoState ε α β (l * c) (l * h) hε hα hβ).deltaMinus () .cont .stop ↔
      0 ≤ (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop := by
  rw [twoState_deltaMinus_scale]
  exact mul_nonneg_iff_of_pos_left hl

/-- **T9(d), the band.** Under `0 < ε`, `0 < β`, `0 < c`: the source's band
`((1 − ε)/ε)(α/β) < h/c < (1 − ε)/ε` is exactly `0 < Δ₋ ∧ 0 < E_μ[X]` — "the button can flip
the decision" (the continue-by-default regime made strict on the prior side, plus strict D1).
Source: [[corr-wf14b-inventory]] 005(d) / legitimacy-general-final.md Statement 4(d) and check Y2 (the "live band" `((1−ε)/ε)(α/β) < h₀/c₀ < (1−ε)/ε`, merged into the general-object final by the inventory; not in general-object-final.md S3/D10 themselves)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoState_band_iff (hε0 : 0 < ε) (hβ0 : 0 < β) (hc : 0 < c) (o₀ : Obs) :
    ((1 - ε) / ε * (α / β) < h / c ∧ h / c < (1 - ε) / ε) ↔
      (0 < (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop ∧
        0 < expect (twoPoint ε hε) ((twoState ε α β c h hε hα hβ).Xo () o₀ .cont .stop)) := by
  rw [twoState_deltaMinus_pos_iff, twoState_expect_Xo, div_mul_div_comm,
    div_lt_div_iff₀ (mul_pos hε0 hβ0) hc, div_lt_div_iff₀ hc hε0]
  constructor <;> rintro ⟨H1, H2⟩ <;> exact ⟨by linarith, by linarith⟩

/-! ## T12 (stretch) — the class-threshold trajectory -/

/-- **T12.** If the false-press rate tracks the error rate as `α_t = ε_t/2`, the threshold
`ε*(ε/2, β, c, h)` stays below `ε` whenever `c < 2βh` — one algebraic lemma behind the six
cells of `check_erosion.py`.
Source: [[corr-wf14b-inventory]] 033 / channel-final.md S12(c), P10 (`α_t = ε_t/2`)
Kind: L (one line of algebra; relabelled from the mandate's P in repair round 1)
Fidelity: exact
Hyps: (a) only -/
theorem epsStar_half_lt (hε0 : 0 < ε) (hc : 0 ≤ c) (hβ0 : 0 < β) (hh : 0 < h) (hcond : c < 2 * β * h) :
    epsStar (ε / 2) β c h < ε := by
  unfold epsStar
  have hden : 0 < ε / 2 * c + β * h :=
    add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) hc) (mul_pos hβ0 hh)
  rw [div_lt_iff₀ hden]
  have h1 := mul_lt_mul_of_pos_left hcond hε0
  have h2 := mul_nonneg (mul_nonneg hε0.le hε0.le) hc
  linarith

end TwoStateForms

end Cleanroom.Found.CorrThreeStep
