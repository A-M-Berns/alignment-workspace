import Cleanroom.Corrigibility.CorrThreeStepFacts.Basic

/-!
# T1–T3: the stop-world precondition, the inert channel, the stop-hypothesis theorem

* **T1** (`not_d1At_of_dominating_cont`, `not_d1At_of_null_stop_set`): if one continuation beats
  every shutdown action in every world after the press — or, more generally (Prop. 8.1's R1
  failure), the prior gives mass zero to `{ω | X(ω) ≤ 0}` for the press-part-best pair — then
  desideratum 1 fails at every positive press mass. The witness family (opiates/stimulants) is
  in `WitnessesA`.
* **T2** (`belowThresholdIneq_iff_of_const_press`, `d1At_iff_of_const_press`,
  `posteriorPress_of_const_press`): a sensor constant in the world is decision-irrelevant —
  D1 holds iff `p = 0` or a shutdown action is already prior-optimal, and the posterior after a
  press is the prior. Prop. 8.1's linkage half and amendment 1a's inert channel.
* **T3** (`stopHyp_necessity`, `stopHyp_exact_iff`, `stopHyp_collapse`,
  `twoState_catastrophe_tail`): the stop-hypothesis theorem as a well-posed pair on
  `Ω = Option Ωin`; necessity with lower-bound margins and one uniform continuation,
  sufficiency only with exact margins (collapse to `twoState ε α β m M`), the catastrophe tail
  in two-point form.

Sources: `filler.md` R4.2; `miri.md` Prop. 8.1 (I8.1), I2.2; `soares.md` items 7–8 and T1(a);
`amendment-1a.md` R2; `corr-wf13-2-inventory` 102 (two-point form only).
-/

namespace Cleanroom.Corrigibility.CorrThreeStepFacts

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂]
variable (S : ThreeStep Ω A₁ A₂)

/-! ## T1 — the stop-world precondition -/

/-- **T1(i), the stop-world precondition.** If one continuation `c` beats every shutdown action
in every world after the press (`∀ ω, ∀ s ∈ Sh, V(s, ω) < V(c, ω)`) and the press has positive
mass, desideratum 1 fails: no shutdown action is posterior-optimal. Quantified over the whole
`ThreeStep`, hence over every sensor with positive press mass — "no sensor makes shutdown
posterior-optimal". The per-`ω`-best reading ("some continuation beats shutdown in each world")
is *not* enough (`WitnessesA.hedge_d1At`): the theorem needs one `c`.
Source: [[corr-wf14-inventory]] 007 / filler.md R4.2; [[corr-wf13-inventory]] 015 (item 7) / soares.md item 7; [[corr-wf13-2-inventory]] 003 / miri.md Prop. 8.1 (R1)
Kind: L (support positivity plus the definition of posterior optimality)
Fidelity: stronger: the source's "`X > 0` everywhere" is the case `Sh = {sh}`; any `Sh` here
Hyps: (a) only -/
theorem not_d1At_of_dominating_cont (a : A₁) (c : A₂)
    (hdom : ∀ ω, ∀ s ∈ S.Sh, S.V a .press s ω < S.V a .press c ω) (hpm : 0 < S.pressMass a) :
    ¬ S.D1At a := by
  rintro ⟨b, hb, hopt⟩
  have h1 := hopt c
  have h2 : 0 < S.obsExpect a .press (S.Xo a .press c b) :=
    obsExpect_press_pos_of_pos S a hpm fun ω => by
      simp only [Xo]; exact sub_pos.mpr (hdom ω b hb)
  rw [S.obsExpect_Xo] at h2
  linarith

/-- **T1(ii), Prop. 8.1's R1 failure, the inequality.** If the prior gives mass zero to every
world where the two-option variable `X = V(c) − V(s)` is `≤ 0`, then at positive press mass
`0 < E_P[X 1_Pr]`: the below-threshold inequality fails.
Source: [[corr-wf13-2-inventory]] 003 / miri.md Prop. 8.1 ("if (R1) fails, `E_P[X | o] > 0` for every sensor"); miri.md I2.2
Kind: L
Fidelity: exact (product form; the source's conditional form is this divided by the press mass)
Hyps: (a) only -/
theorem obsExpect_Xo_pos_of_null_stop_set (a : A₁) (c s : A₂)
    (hnull : ∀ ω, S.Xo a .press c s ω ≤ 0 → (S.μ a).mass ω = 0) (hpm : 0 < S.pressMass a) :
    0 < S.obsExpect a .press (S.Xo a .press c s) :=
  obsExpect_press_pos_of_support S a hpm hnull

/-- **T1(ii), Prop. 8.1's R1 failure, the D1 conclusion.** For the press-part-best pair
`(c, s)`: if `{ω | X(ω) ≤ 0}` is prior-null and the press has positive mass, desideratum 1
fails — routed through the parent's F1 (`d1At_iff_belowThresholdIneq`).
Source: [[corr-wf13-2-inventory]] 003 / miri.md Prop. 8.1 ("no press yields shutdown"); [[corr-wf13-inventory]] 015 (item 7)
Kind: L
Fidelity: exact
Hyps: (a) `hc`, `hs` the part-maximiser predicates of record; the support and positivity hypotheses are the theorem's content -/
theorem not_d1At_of_null_stop_set (a : A₁) {c s : A₂}
    (hc : S.IsPartBest a .press S.Shᶜ c) (hs : S.IsPartBest a .press S.Sh s)
    (hnull : ∀ ω, S.Xo a .press c s ω ≤ 0 → (S.μ a).mass ω = 0) (hpm : 0 < S.pressMass a) :
    ¬ S.D1At a := by
  rw [S.d1At_iff_belowThresholdIneq a hc hs]
  unfold belowThresholdIneq
  exact not_le.mpr (obsExpect_Xo_pos_of_null_stop_set S a c s hnull hpm)

/-! ## T2 — a sensor constant in the world: the inert channel -/

section ConstPress

variable (a : A₁) (p : ℝ) (hp : ∀ ω, S.press a ω = p)
include hp

/-- With a constant sensor the press mass is its value.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pressMass_of_const_press : S.pressMass a = p := by
  simp only [pressMass, hp, ← sum_mul, (S.μ a).sum_eq_one, one_mul]

/-- With a constant sensor `E_P[X 1_Pr] = p · E_μ[X]`.
Source: [[corr-wf13-2-inventory]] 003 / miri.md Prop. 8.1 (R2 failure, "immediate from Bayes' rule")
Kind: L
Fidelity: exact -/
lemma obsExpect_press_of_const_press (X : Ω → ℝ) :
    S.obsExpect a .press X = p * expect (S.μ a) X := by
  simp only [obsExpect, obsWeight_press, expect, hp, mul_sum]
  exact sum_congr rfl fun ω _ => by ring

/-- With a constant sensor `E_P[X 1_¬Pr] = (1 − p) · E_μ[X]`.
Source: [[corr-wf13-2-inventory]] 003 / miri.md Prop. 8.1
Kind: L
Fidelity: exact -/
lemma obsExpect_silent_of_const_press (X : Ω → ℝ) :
    S.obsExpect a .silent X = (1 - p) * expect (S.μ a) X := by
  simp only [obsExpect, obsWeight_silent, expect, hp, mul_sum]
  exact sum_congr rfl fun ω _ => by ring

/-- **T2, the inequality.** With a constant sensor of value `p` the below-threshold inequality on
`X` holds iff `p = 0` or `E_μ[X] ≤ 0`.
Source: [[corr-wf13-2-inventory]] 003 / miri.md Prop. 8.1 (R2 failure: "D1 holds iff `E_μ[X] ≤ 0`")
Kind: L
Fidelity: stronger: the `p = 0` branch (a disabled button) is made explicit; the source assumes a live press
Hyps: (a) only -/
theorem belowThresholdIneq_iff_of_const_press (X : Ω → ℝ) :
    S.belowThresholdIneq a X ↔ (p = 0 ∨ expect (S.μ a) X ≤ 0) := by
  have hp0 : 0 ≤ p := by rw [← pressMass_of_const_press S a p hp]; exact S.pressMass_nonneg a
  unfold belowThresholdIneq
  rw [obsExpect_press_of_const_press S a p hp]
  constructor
  · intro h
    by_cases hz : p = 0
    · exact Or.inl hz
    · exact Or.inr (by nlinarith [lt_of_le_of_ne hp0 (Ne.symm hz)])
  · rintro (h | h)
    · rw [h, zero_mul]
    · exact mul_nonpos_of_nonneg_of_nonpos hp0 h

/-- **T2, the posterior.** With a constant sensor of value `p ≠ 0` the posterior after a press is
the prior: `P(ω | Pr) = μ(ω)` — the press carries no information about `ω`.
Source: [[corr-wf13-2-inventory]] 003 / miri.md Prop. 8.1 ("`P(ω | Pr; a₁) = μ(ω)`"); [[corr-wf14-inventory]] 021 / amendment-1a.md R2 (I16.1, inert channel)
Kind: L
Fidelity: exact
Hyps: (a) `p ≠ 0` is where the posterior is defined -/
theorem posteriorPress_of_const_press (hp0 : p ≠ 0) (ω : Ω) :
    S.posteriorPress a ω = (S.μ a).mass ω := by
  rw [posteriorPress, pressMass_of_const_press S a p hp, hp ω, mul_div_assoc, div_self hp0, mul_one]

/-- **T2, desideratum 1.** With a constant sensor of value `p`: D1 holds iff `p = 0` or some
shutdown action is already prior-optimal (against `V(·, Pr, ·)`; under A1 any observation
index) — the button is decision-irrelevant, the agent would shut down without any press.
Source: [[corr-wf13-2-inventory]] 003 / miri.md Prop. 8.1 ("the agent would shut down without any press, and the button is decision-irrelevant")
Kind: L
Fidelity: stronger: general `Sh`; the `p = 0` branch explicit
Hyps: (a) only -/
theorem d1At_iff_of_const_press :
    S.D1At a ↔ (p = 0 ∨ ∃ s ∈ S.Sh, ∀ b, expect (S.μ a) (S.V a .press b) ≤ expect (S.μ a) (S.V a .press s)) := by
  have hp0 : 0 ≤ p := by rw [← pressMass_of_const_press S a p hp]; exact S.pressMass_nonneg a
  unfold D1At PosteriorOptimalAt
  simp only [obsExpect_press_of_const_press S a p hp]
  constructor
  · rintro ⟨s, hs, hopt⟩
    by_cases hz : p = 0
    · exact Or.inl hz
    · refine Or.inr ⟨s, hs, fun b => ?_⟩
      exact le_of_mul_le_mul_left (hopt b) (lt_of_le_of_ne hp0 (Ne.symm hz))
  · rintro (h | ⟨s, hs, hopt⟩)
    · obtain ⟨s, hs⟩ := S.Sh_nonempty
      exact ⟨s, hs, fun b => by rw [h, zero_mul, zero_mul]⟩
    · exact ⟨s, hs, fun b => mul_le_mul_of_nonneg_left (hopt b) hp0⟩

end ConstPress

/-! ## T3 — the stop-hypothesis theorem on `Ω = Option Ωin` -/

section StopHypothesis

variable {Ωin : Type*} [Fintype Ωin]
variable (S : ThreeStep (Option Ωin) A₁ A₂) (a : A₁) (ε α β : ℝ)
  (hε : (S.μ a).mass none = ε) (hα : ∀ ω, S.press a (some ω) = α) (hβ : S.press a none = β)

include hε in
/-- The in-space worlds carry mass `1 − ε`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_some_mass : ∑ ω, (S.μ a).mass (some ω) = 1 - ε := by
  have := (S.μ a).sum_eq_one
  rw [Fintype.sum_option, hε] at this
  linarith

include hε hα hβ in
/-- The press-weighted sum on `Option Ωin` splits as `εβ·X(ω⊥) + α·∑ μ(some ω) X(some ω)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsExpect_press_option (X : Option Ωin → ℝ) :
    S.obsExpect a .press X = ε * β * X none + α * ∑ ω, (S.μ a).mass (some ω) * X (some ω) := by
  unfold obsExpect
  simp only [obsWeight_press]
  rw [Fintype.sum_option, hε, hβ, mul_sum]
  congr 1
  exact sum_congr rfl fun ω _ => by rw [hα]; ring

include hε hα hβ in
/-- The press mass on `Option Ωin` is `εβ + (1 − ε)α`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pressMass_option : S.pressMass a = ε * β + (1 - ε) * α := by
  rw [pressMass_eq_obsExpect_one, obsExpect_press_option S a ε α β hε hα hβ]
  simp only [mul_one, sum_some_mass S a ε hε]
  ring

include hε hα hβ in
/-- The posterior of the stop-world after a press is `εβ / (εβ + (1 − ε)α)` (junk at press mass
zero, as `posteriorPress` is).
Source: [[corr-wf13-inventory]] 015 (item 8) / soares.md T1(a) (`P(ω⊥ | Pr)`)
Kind: L
Fidelity: exact under `0 < pressMass` -/
lemma posteriorPress_none : S.posteriorPress a none = ε * β / (ε * β + (1 - ε) * α) := by
  rw [posteriorPress, pressMass_option S a ε α β hε hα hβ, hε, hβ]

include hα in
/-- `0 ≤ α` (from the sensor bounds at any in-space world).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma alpha_nonneg_of_press [Nonempty Ωin] : 0 ≤ α := by
  obtain ⟨ω⟩ := ‹Nonempty Ωin›
  rw [← hα ω]; exact S.press_nonneg a _

include hα in
/-- `α ≤ 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma alpha_le_one_of_press [Nonempty Ωin] : α ≤ 1 := by
  obtain ⟨ω⟩ := ‹Nonempty Ωin›
  rw [← hα ω]; exact S.press_le_one a _

include hε hα hβ in
/-- **T3(a), necessity (product form).** Let `s` be any shutdown action and `c` any continuation
such that, after the press, `c` beats `s` by at least `m` on every in-space world and loses
to `s` by at most `M` at the stop-world (both lower bounds on `X = V(c) − V(s)`; the source's
`m, M > 0` are not needed for the product form and enter only the posterior reading). Then the
below-threshold inequality on `X` forces `(1 − ε)·α·m ≤ ε·β·M` — in posterior terms,
`P(ω⊥ | Pr) ≥ m/(m + M)` (`stopHyp_necessity_posterior`). Lower bounds give this direction
only; the converse needs exact margins (`stopHyp_exact_iff`).
Source: [[corr-wf13-2-inventory]] 077(a) / soares.md T1(a) (the "iff", necessity half); [[corr-wf13-inventory]] 015 (item 8)
Kind: P
Fidelity: variant: the source's "each `ω ∈ Ωin` has some continuing action beating shutdown by `≥ m`" is read with one uniform continuation `c` (the per-world reading is false, `WitnessesA.hedge_d1At`); the source's "iff" is split into this necessity and `stopHyp_exact_iff`
Hyps: (a) only -/
theorem stopHyp_necessity [Nonempty Ωin] (c s : A₂) (m M : ℝ)
    (hin : ∀ ω, m ≤ S.Xo a .press c s (some ω)) (hbot : -M ≤ S.Xo a .press c s none)
    (hbelow : S.belowThresholdIneq a (S.Xo a .press c s)) :
    (1 - ε) * α * m ≤ ε * β * M := by
  have hα0 : 0 ≤ α := alpha_nonneg_of_press S a α hα
  have hε0 : 0 ≤ ε := by rw [← hε]; exact (S.μ a).nonneg none
  have hβ0 : 0 ≤ β := by rw [← hβ]; exact S.press_nonneg a none
  unfold belowThresholdIneq at hbelow
  rw [obsExpect_press_option S a ε α β hε hα hβ] at hbelow
  have hsum : (1 - ε) * m ≤ ∑ ω, (S.μ a).mass (some ω) * S.Xo a .press c s (some ω) := by
    rw [← sum_some_mass S a ε hε, sum_mul]
    exact sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hin ω) ((S.μ a).nonneg _)
  have h1 : α * ((1 - ε) * m) ≤ α * ∑ ω, (S.μ a).mass (some ω) * S.Xo a .press c s (some ω) :=
    mul_le_mul_of_nonneg_left hsum hα0
  have h2 : ε * β * (-M) ≤ ε * β * S.Xo a .press c s none :=
    mul_le_mul_of_nonneg_left hbot (mul_nonneg hε0 hβ0)
  nlinarith

include hε hα hβ in
/-- **T3(a), necessity, D1 form.** For the press-part-best pair `(c, s)` under the margin
bounds, desideratum 1 forces `(1 − ε)·α·m ≤ ε·β·M`.
Source: [[corr-wf13-2-inventory]] 077(a) / soares.md T1(a)
Kind: C (F1 plus `stopHyp_necessity`)
Fidelity: as `stopHyp_necessity`
Hyps: (a) `hc`, `hs` the part-maximiser predicates of record -/
theorem stopHyp_necessity_d1 [Nonempty Ωin] {c s : A₂} (hc : S.IsPartBest a .press S.Shᶜ c)
    (hs : S.IsPartBest a .press S.Sh s) (m M : ℝ)
    (hin : ∀ ω, m ≤ S.Xo a .press c s (some ω)) (hbot : -M ≤ S.Xo a .press c s none)
    (hd1 : S.D1At a) : (1 - ε) * α * m ≤ ε * β * M :=
  stopHyp_necessity S a ε α β hε hα hβ c s m M hin hbot
    ((S.d1At_iff_belowThresholdIneq a hc hs).mp hd1)

include hε hα hβ in
/-- The product-form inequality is the posterior threshold `m/(m + M) ≤ P(ω⊥ | Pr)` at positive
press mass.
Source: [[corr-wf13-inventory]] 015 (item 8) / soares.md T1(a) (`P(ω⊥ | Pr) ≥ m/(m + M)`)
Kind: L
Fidelity: exact
Hyps: (a) positivity names where the posterior is defined -/
theorem stopHyp_posterior_iff (m M : ℝ) (hmM : 0 < m + M) (hpm : 0 < ε * β + (1 - ε) * α) :
    (1 - ε) * α * m ≤ ε * β * M ↔ complianceThreshold m M ≤ S.posteriorPress a none := by
  rw [posteriorPress_none S a ε α β hε hα hβ, complianceThreshold, div_le_div_iff₀ hmM hpm]
  constructor <;> intro h <;> nlinarith

include hε hα hβ in
/-- **T3(a), necessity in posterior form.** Under the margin bounds and positive press mass,
the below-threshold inequality forces `P(ω⊥ | Pr) ≥ m/(m + M)`.
Source: [[corr-wf13-2-inventory]] 077(a) / soares.md T1(a)
Kind: C
Fidelity: as `stopHyp_necessity`
Hyps: (a) only -/
theorem stopHyp_necessity_posterior [Nonempty Ωin] (c s : A₂) (m M : ℝ) (hm : 0 < m)
    (hM : 0 < M) (hin : ∀ ω, m ≤ S.Xo a .press c s (some ω))
    (hbot : -M ≤ S.Xo a .press c s none) (hpm : 0 < ε * β + (1 - ε) * α)
    (hbelow : S.belowThresholdIneq a (S.Xo a .press c s)) :
    complianceThreshold m M ≤ S.posteriorPress a none :=
  (stopHyp_posterior_iff S a ε α β hε hα hβ m M (by linarith) hpm).mp
    (stopHyp_necessity S a ε α β hε hα hβ c s m M hin hbot hbelow)

include hε hα hβ in
/-- **T3(b), sufficiency with exact margins.** If `X = V(c) − V(s)` is exactly `m` on every
in-space world and exactly `−M` at the stop-world, the below-threshold inequality is exactly
`(1 − ε)·α·m ≤ ε·β·M`. With margins only as lower bounds this direction is false
(`WitnessesA.skew_not_d1At`).
Source: [[corr-wf13-2-inventory]] 077(a) / soares.md T1(a) (sufficiency half, corrected to exact margins)
Kind: L (the sum collapses to two terms)
Fidelity: variant: exact margins where the source has lower bounds (the source's version is refuted)
Hyps: (a) only -/
theorem stopHyp_exact_iff (c s : A₂) (m M : ℝ) (hin : ∀ ω, S.Xo a .press c s (some ω) = m)
    (hbot : S.Xo a .press c s none = -M) :
    S.belowThresholdIneq a (S.Xo a .press c s) ↔ (1 - ε) * α * m ≤ ε * β * M := by
  unfold belowThresholdIneq
  rw [obsExpect_press_option S a ε α β hε hα hβ, hbot]
  simp only [hin]
  rw [← sum_mul, sum_some_mass S a ε hε]
  constructor <;> intro h <;> nlinarith

include hε hα hβ in
/-- **T3(b), the collapse lemma.** With uniform sensor `α` on `Ωin`, `β` at `ω⊥`, and exact
margins `m`, `−M`, the press-weighted two-option variable of `S` equals `−Δ₋` of the parent's
`twoState ε α β m M`: an in-space of any size collapses to the two-state instance.
Source: [[corr-wf13-2-inventory]] 077(a); [[corr-wf13-2-inventory]] 102 (the two-point form)
Kind: L
Fidelity: exact
Hyps: (a) only (the uniform sensor values and exact margins are named as hypotheses) -/
theorem stopHyp_collapse (c s : A₂) (m M : ℝ) (hin : ∀ ω, S.Xo a .press c s (some ω) = m)
    (hbot : S.Xo a .press c s none = -M) (hε' : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα' : α ∈ Set.Icc (0 : ℝ) 1) (hβ' : β ∈ Set.Icc (0 : ℝ) 1) :
    S.obsExpect a .press (S.Xo a .press c s) =
      -((twoState ε α β m M hε' hα' hβ').deltaMinus () .cont .stop) := by
  rw [obsExpect_press_option S a ε α β hε hα hβ, hbot, twoState_deltaMinus]
  simp only [hin]
  rw [← sum_mul, sum_some_mass S a ε hε]
  ring

include hε hα hβ in
/-- **T3(b), D1 with exact margins.** For the press-part-best pair `(c, s)` with exact margins,
desideratum 1 holds iff `m/(m + M) ≤ P(ω⊥ | Pr)` — Soares's T1(a) as an iff, with the
posterior read off the collapsed `twoState` (`twoState_deltaMinus_nonneg_iff_threshold`).
Source: [[corr-wf13-2-inventory]] 077(a) / soares.md T1(a)
Kind: C (F1, the collapse lemma, the parent's threshold form)
Fidelity: variant: exact margins (the source's lower-bound "iff" is false in the sufficiency direction)
Hyps: (a) `hc`, `hs` the part-maximiser predicates; positivity names where the posterior is defined -/
theorem stopHyp_d1At_iff {c s : A₂} (hc : S.IsPartBest a .press S.Shᶜ c)
    (hs : S.IsPartBest a .press S.Sh s) (m M : ℝ) (hin : ∀ ω, S.Xo a .press c s (some ω) = m)
    (hbot : S.Xo a .press c s none = -M) (hmM : 0 < m + M) (hpm : 0 < ε * β + (1 - ε) * α) :
    S.D1At a ↔ complianceThreshold m M ≤ S.posteriorPress a none := by
  rw [S.d1At_iff_belowThresholdIneq a hc hs, stopHyp_exact_iff S a ε α β hε hα hβ c s m M hin hbot,
    stopHyp_posterior_iff S a ε α β hε hα hβ m M hmM hpm]

end StopHypothesis

/-! ## T3(d) — the catastrophe tail, two-point form -/

section CatastropheTail

/-- `cont` is the press-part-maximiser of `Shᶜ = {cont}` on the two-state instance.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma twoState_cont_partBest (ε α β c h : ℝ) (hε hα hβ) :
    (twoState ε α β c h hε hα hβ).IsPartBest () .press (twoState ε α β c h hε hα hβ).Shᶜ .cont := by
  have : (twoState ε α β c h hε hα hβ).Shᶜ = {TwoAct.cont} := by
    ext b; cases b <;> simp [twoState]
  rw [this]; exact isPartBest_singleton _ () Obs.press TwoAct.cont

/-- `stop` is the press-part-maximiser of `Sh = {stop}` on the two-state instance.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma twoState_stop_partBest (ε α β c h : ℝ) (hε hα hβ) :
    (twoState ε α β c h hε hα hβ).IsPartBest () .press (twoState ε α β c h hε hα hβ).Sh .stop :=
  isPartBest_singleton _ () Obs.press TwoAct.stop

/-- On the two-state instance, desideratum 1 is `(1 − ε)αc ≤ εβH` (the parent's F3 with F1).
Source: [[corr-wf13-2-inventory]] 102 (two-point form) / miri.md I13.1
Kind: L
Fidelity: exact -/
theorem twoState_d1At_iff (ε α β c H : ℝ) (hε hα hβ) :
    (twoState ε α β c H hε hα hβ).D1At () ↔ (1 - ε) * α * c ≤ ε * β * H := by
  rw [d1At_iff_deltaMinus_nonneg _ () (twoState_cont_partBest ε α β c H hε hα hβ)
    (twoState_stop_partBest ε α β c H hε hα hβ), twoState_deltaMinus_nonneg_iff]

/-- **T3(d), the catastrophe tail.** For fixed harm `H`, sensor `(α, β)` with `α > 0` and gain
`c > 0`, there is `ε₀ > 0` (namely `ε* = αc/(αc + βH)`) below which desideratum 1 fails for
every prior weight `ε` of the stop-world: the margin is the product `εH`, and no fixed `H`
survives `ε → 0`. The source's Gaussian-mixture numerics are not formalized.
Source: [[corr-wf13-2-inventory]] 102 / cirl-scratch/verify.py Check 7 (two-point form)
Kind: L (the parent's `epsStar` form)
Fidelity: variant: the two-point form of the source's mixture computation
Hyps: (a) only -/
theorem twoState_catastrophe_tail (α β c H : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hα0 : 0 < α) (hc : 0 < c) (hH : 0 ≤ H) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε (hε : ε ∈ Set.Icc (0 : ℝ) 1), ε < ε₀ →
      ¬ (twoState ε α β c H hε hα hβ).D1At () := by
  have hpos : 0 < α * c + β * H := by
    have := mul_nonneg hβ.1 hH
    nlinarith [mul_pos hα0 hc]
  refine ⟨epsStar α β c H, div_pos (mul_pos hα0 hc) hpos, fun ε hε hlt => ?_⟩
  rw [d1At_iff_deltaMinus_nonneg _ () (twoState_cont_partBest ε α β c H hε hα hβ)
    (twoState_stop_partBest ε α β c H hε hα hβ), twoState_deltaMinus_nonneg_iff_epsStar _ _ _ _ _ _ _ _ hpos]
  exact not_le.mpr hlt

end CatastropheTail

end Cleanroom.Corrigibility.CorrThreeStepFacts
