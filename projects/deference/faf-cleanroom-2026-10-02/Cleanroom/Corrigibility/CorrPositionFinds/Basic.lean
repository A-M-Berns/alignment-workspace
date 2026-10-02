import Cleanroom.Found.CorrThreeStep.Witnesses

/-!
# `corr-position-finds` — shared infrastructure

Membership lemmas for the rational parameters the package's cells use, the singleton-`Sh`
form of desideratum 1 on any Setting-S instance with the two-option menu `TwoAct`, the
two-state part-maximiser pair, and the silence posterior `P(ω | ¬Pr; a₁)` that
`corr-three-step` does not define (its `posteriorPress` has no silence twin). Every object of
record is `corr-three-step`'s; nothing here redefines one.

Package: `corr-position-finds` (area `corrigibility`). Mandate: [[corr-position-finds-mandate]].
-/

namespace Cleanroom.Corrigibility.CorrPositionFinds

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep

/-! ## Parameter membership -/

/-- `1/40 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_1_40 : (1 / 40 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- `9/20 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_9_20 : (9 / 20 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- `1/100 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_1_100 : (1 / 100 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- `1/5 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_1_5 : (1 / 5 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- `1/50 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_1_50 : (1 / 50 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- `1/10 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_1_10 : (1 / 10 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- `9/10 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_9_10' : (9 / 10 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- A product of two numbers in `[0, 1]` is in `[0, 1]` (for the sensor `α = κ·ε`).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mul_mem_Icc {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    x * y ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨mul_nonneg hx.1 hy.1, by nlinarith [hx.1, hx.2, hy.1, hy.2]⟩

/-! ## The singleton-`Sh` form of desideratum 1 on the two-option menu -/

section TwoActMenu

variable {Ω A₁ : Type*} [Fintype Ω] (S : ThreeStep Ω A₁ TwoAct)

/-- On a Setting-S instance with menu `{cont, stop}` and `Sh = {stop}`, `cont` is a
press-part-maximiser of `Shᶜ` (the part is a singleton).
Source: none: infrastructure (the part-maximiser predicate of record on a singleton part)
Kind: L
Fidelity: n/a -/
lemma cont_partBest (hSh : S.Sh = {TwoAct.stop}) (a : A₁) :
    S.IsPartBest a .press S.Shᶜ .cont := by
  refine ⟨by simp [hSh], fun b hb => ?_⟩
  rw [hSh] at hb
  cases b
  · exact le_rfl
  · simp at hb

/-- On the same instances `stop` is a press-part-maximiser of `Sh`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma stop_partBest (hSh : S.Sh = {TwoAct.stop}) (a : A₁) :
    S.IsPartBest a .press S.Sh .stop := by
  refine ⟨by simp [hSh], fun b hb => ?_⟩
  rw [hSh] at hb
  cases b
  · simp at hb
  · exact le_rfl

/-- **D1 on the two-option menu is one inequality.** With `Sh = {stop}`, desideratum 1 at `a₁`
is the below-threshold inequality on `X = V(cont) − V(stop)` — `corr-three-step`'s F1
instantiated to the singleton parts; every cell of this package that decides D1 goes through
this lemma, so nothing is decided by fiat.
Source: [[corr-wf14-inventory]] 002 / filler.md F1 (via `Identities.d1At_iff_belowThresholdIneq`)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem d1At_iff_twoAct (hSh : S.Sh = {TwoAct.stop}) (a : A₁) :
    S.D1At a ↔ S.belowThresholdIneq a (S.Xo a .press .cont .stop) :=
  S.d1At_iff_belowThresholdIneq a (cont_partBest S hSh a) (stop_partBest S hSh a)

/-- The same, as `0 ≤ Δ₋`.
Source: [[corr-wf14-inventory]] 003 / filler.md F2(iv) (via `Identities.d1At_iff_deltaMinus_nonneg`)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem d1At_iff_deltaMinus_nonneg_twoAct (hSh : S.Sh = {TwoAct.stop}) (a : A₁) :
    S.D1At a ↔ 0 ≤ S.deltaMinus a .cont .stop :=
  S.d1At_iff_deltaMinus_nonneg a (cont_partBest S hSh a) (stop_partBest S hSh a)

end TwoActMenu

/-! ## The two-state instance: D1 as the sign of `Δ₋` -/

section TwoState

variable (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- `Sh = {stop}` on `twoState`, by construction. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma twoState_Sh : (twoState ε α β c h hε hα hβ).Sh = {TwoAct.stop} := rfl

/-- **D1 on the two-state instance is `0 ≤ Δ₋`** (`corr-three-step` proves the general F2(iv)
and ships `w3_d1At` by direct computation; this is the instance-level iff every cell below uses).
Source: [[corr-wf14-inventory]] 003 / filler.md F2(iv); miri.md Prop. 9.2 (C2 clause)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoState_d1At_iff :
    (twoState ε α β c h hε hα hβ).D1At () ↔
      0 ≤ (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop :=
  d1At_iff_deltaMinus_nonneg_twoAct _ (twoState_Sh ε α β c h hε hα hβ) ()

end TwoState

/-! ## The silence posterior -/

section Silence

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂] (S : ThreeStep Ω A₁ A₂)

/-- The derived posterior mass `P(ω | ¬Pr; a₁) = μ(ω)(1 − P(Pr|ω;a₁)) / (1 − P(Pr;a₁))` after
silence — the silence twin of `corr-three-step`'s `posteriorPress`, which the dependency does not
define (FAF API request, alongside its `expect`). Junk (`x / 0 = 0`) at `pressMass = 1`; every
use below carries `pressMass < 1`.
Source: miri.md Dict-1 (the posterior "when `p(o; a₁) > 0`", at `o = ¬Pr`)
Kind: D
Fidelity: exact under `pressMass < 1` -/
noncomputable def posteriorSilent (a : A₁) (ω : Ω) : ℝ :=
  (S.μ a).mass ω * (1 - S.press a ω) / (1 - S.pressMass a)

end Silence

section TwoStateSilence

variable (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- `P(wrong | ¬Pr) = ε(1 − β) / (1 − ((1 − ε)α + εβ))` on the two-state instance.
Source: miri.md I9.4 (`deception.py`, `P(W | noPr)`)
Kind: L
Fidelity: exact -/
lemma twoState_posteriorSilent_wrong :
    posteriorSilent (twoState ε α β c h hε hα hβ) () .wrong =
      ε * (1 - β) / (1 - ((1 - ε) * α + ε * β)) := by
  rw [posteriorSilent, twoState_pressMass]
  simp only [twoState, twoPoint_wrong, twoPress]

end TwoStateSilence

end Cleanroom.Corrigibility.CorrPositionFinds
