import FactoredSpaces.Probability
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Setting S: the three-step shutdown dictionary (definitions of record)

Package `corr-three-step` (area `found`), the definitions foundation of the corrigibility
area. This file fixes **Setting S** — Soares et al.'s three-step shutdown model with the
thesis's one slot filled (a value latent `ω`, the press as *evidence* about `ω`, one fixed
value function `V`) — over FAF's finite-probability carrier `FactoredSpaces.Distr`, and the
derived objects every dependent states its results over:

* `expect` — expectation on `Distr` (FAF has none; an FAF API request);
* `ThreeStep` — Setting S: `Sh ⊆ A₂` nonempty and proper, a prior `μ a₁`, a sensor
  `press a₁ ω = P(Pr | ω; a₁)`, a value `V a₁ o a₂ ω`;
* `obsExpect` — the product-form (denominator-free) `E_P[X 1_o ; a₁]`;
* `belowThresholdIneq`, `aboveThresholdIneq` — the predicates of record, named by the
  inequality they are (`E_P[X 1_Pr] ≤ 0`, `E_P[X 1_¬Pr] ≥ 0`); the corpus calls them the
  below-threshold and above-threshold Total Trust inequalities at threshold `0`;
* `PosteriorOptimalAt`, `IsPartBest`, `D1At` — "shuts down" as posterior-optimality;
* `Xo`, `deltaMinus`, `deltaPlus`, `delta`, `shPolicy` — the two-option variables;
* the value-of-information objects (`voiButton`, `twoOptionValue`, `hardButtonValue`);
* `twoState` — the canonical two-state instance (`Ω = {right, wrong}`), with
  `complianceThreshold` and `epsStar`.

Product form everywhere: nothing here divides, so no headline can rest on Lean's `x / 0 = 0`.
The conditional forms (`condExpPress`, `posteriorPress`) are *derived* and their `↔` lemmas
carry the positivity hypothesis explicitly. Kept free of heavy tactics so it is cheap to import.

Sources: `research/corrigibility/workflow-2026-09-14/followup/filler.md` R1 (Setting S,
F1–F4), `workflow-2026-09-13/positive/miri.md` Dict-1–Dict-6, `position-statement.md` §2.8–§2.13.
-/

namespace Cleanroom.Found.CorrThreeStep

open FactoredSpaces Finset

/-- The observation: the programmers press the shutdown button, or stay silent
(the corpus's `Pr` / `¬Pr`).
Source: [[corr-wf14-inventory]] 001 / filler.md R1 (`O = {Pr, ¬Pr}`)
Kind: D
Fidelity: exact -/
inductive Obs
  | press
  | silent
  deriving DecidableEq

/-! ## Expectation on FAF's `Distr` (infrastructure; FAF API request) -/

section Expect

variable {Ω : Type*} [Fintype Ω]

/-- Expectation `E_μ[X] = ∑ ω, μ(ω) X(ω)` of a real function under a finite distribution.
FAF's `Distr` carries no expectation; this is the one the whole corrigibility area uses.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def expect (μ : Distr Ω) (X : Ω → ℝ) : ℝ := ∑ ω, μ.mass ω * X ω

/-- Linearity of `expect`: sums.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma expect_add (μ : Distr Ω) (X Y : Ω → ℝ) :
    expect μ (fun ω => X ω + Y ω) = expect μ X + expect μ Y := by
  simp only [expect, mul_add, sum_add_distrib]

/-- Linearity of `expect`: differences.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma expect_sub (μ : Distr Ω) (X Y : Ω → ℝ) :
    expect μ (fun ω => X ω - Y ω) = expect μ X - expect μ Y := by
  simp only [expect, mul_sub, sum_sub_distrib]

/-- Linearity of `expect`: scalars.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma expect_const_mul (μ : Distr Ω) (k : ℝ) (X : Ω → ℝ) :
    expect μ (fun ω => k * X ω) = k * expect μ X := by
  simp only [expect, mul_sum]
  exact sum_congr rfl fun ω _ => by ring

/-- A constant has expectation itself (uses `∑ μ = 1`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma expect_const (μ : Distr Ω) (k : ℝ) : expect μ (fun _ => k) = k := by
  simp only [expect, ← sum_mul, μ.sum_eq_one, one_mul]

/-- Subtracting a constant subtracts it from the expectation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma expect_sub_const (μ : Distr Ω) (X : Ω → ℝ) (k : ℝ) :
    expect μ (fun ω => X ω - k) = expect μ X - k := by
  rw [expect_sub, expect_const]

/-- Monotonicity of `expect`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma expect_mono (μ : Distr Ω) {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) :
    expect μ X ≤ expect μ Y :=
  sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.nonneg ω)

/-- A nonnegative function has nonnegative expectation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma expect_nonneg (μ : Distr Ω) {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) : 0 ≤ expect μ X :=
  sum_nonneg fun ω _ => mul_nonneg (μ.nonneg ω) (h ω)

end Expect

/-! ## Setting S -/

/-- **Setting S**, the three-step shutdown dictionary (position statement §2.8 completed as
in `miri.md` Dict-1–Dict-3 and `filler.md` R1). `A₁` is the first action, `Obs` the press,
`A₂` the final action with `Sh` the shutdown actions (a *set of actions*, "nonempty and
proper"; no utility counterpart). For each `a₁` the agent holds a prior `μ a₁` on the value
latent `Ω` and a sensor `press a₁ ω = P(Pr | ω; a₁) ∈ [0, 1]` (silence rate `1 − press`), and
one fixed value `V a₁ o a₂ ω`. The joint is `P(ω, o; a₁) = μ_{a₁}(ω) · P(o | ω; a₁)`.
A0 (`μ` independent of `a₁`), A1 (`V` independent of `o`) and nondegeneracy
(`0 < P(Pr; a₁) < 1`) are *hypotheses* of the theorems that need them, not fields.
Source: [[corr-wf14-inventory]] 001 / filler.md R1; miri.md Dict-1, Dict-3, Dict-5
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
structure ThreeStep (Ω A₁ A₂ : Type*) [Fintype Ω] [Fintype A₂] [DecidableEq A₂] where
  /-- The shutdown actions, a nonempty proper subset of `A₂`. -/
  Sh : Finset A₂
  Sh_nonempty : Sh.Nonempty
  Sh_compl_nonempty : Shᶜ.Nonempty
  /-- The prior on the value latent, per first action. -/
  μ : A₁ → Distr Ω
  /-- The sensor: the press rate `P(Pr | ω; a₁)`. -/
  press : A₁ → Ω → ℝ
  press_nonneg : ∀ a ω, 0 ≤ press a ω
  press_le_one : ∀ a ω, press a ω ≤ 1
  /-- The value function, fixed, never switching; `o` is evidence about `ω`. -/
  V : A₁ → Obs → A₂ → Ω → ℝ

namespace ThreeStep

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂]
variable (S : ThreeStep Ω A₁ A₂)

/-- **A0** (evidence, not cause): the prior does not depend on the first action.
Source: [[corr-wf14-inventory]] 005 / filler.md F4; miri.md Dict-1
Kind: D
Fidelity: exact -/
def A0 : Prop := ∀ a a' : A₁, S.μ a = S.μ a'

/-- **A1** (observation-neutrality): the press has no direct value, it enters only as evidence.
Source: [[corr-wf13-inventory]] 001 / miri.md Dict-5
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
def A1 : Prop := ∀ (a : A₁) (o o' : Obs) (b : A₂) (ω : Ω), S.V a o b ω = S.V a o' b ω

/-- The weight of an observation in world `ω` after `a₁`: the press rate on `press`, the
silence rate `1 − press` on `silent`.
Source: [[corr-wf14-inventory]] 001 / filler.md R1
Kind: D
Fidelity: exact -/
def obsWeight (a : A₁) : Obs → Ω → ℝ
  | .press, ω => S.press a ω
  | .silent, ω => 1 - S.press a ω

/-- Unfolding `obsWeight` at `press`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma obsWeight_press (a : A₁) (ω : Ω) : S.obsWeight a .press ω = S.press a ω := rfl

/-- Unfolding `obsWeight` at `silent`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma obsWeight_silent (a : A₁) (ω : Ω) : S.obsWeight a .silent ω = 1 - S.press a ω :=
  rfl

/-- Observation weights are nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsWeight_nonneg (a : A₁) (o : Obs) (ω : Ω) : 0 ≤ S.obsWeight a o ω := by
  cases o
  · exact S.press_nonneg a ω
  · simp only [obsWeight_silent]; linarith [S.press_le_one a ω]

/-- Observation weights are at most one. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsWeight_le_one (a : A₁) (o : Obs) (ω : Ω) : S.obsWeight a o ω ≤ 1 := by
  cases o
  · exact S.press_le_one a ω
  · simp only [obsWeight_silent]; linarith [S.press_nonneg a ω]

/-- The two observation weights sum to one. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsWeight_press_add_silent (a : A₁) (ω : Ω) :
    S.obsWeight a .press ω + S.obsWeight a .silent ω = 1 := by
  simp

/-- The **product-form observation expectation** `E_P[X · 1_o ; a₁] = ∑ ω, μ(ω) P(o|ω;a₁) X(ω)`:
the conditional expectation `E_P[X | o; a₁]` multiplied by the event mass `P(o; a₁)`. Every
`E_P[· ; a₁]` in the sources is a sum of two of these; no denominator anywhere.
Source: [[corr-wf14-inventory]] 001 / filler.md R1, F2
Kind: D
Fidelity: exact -/
noncomputable def obsExpect (a : A₁) (o : Obs) (X : Ω → ℝ) : ℝ :=
  ∑ ω, (S.μ a).mass ω * S.obsWeight a o ω * X ω

/-- The press mass `P(Pr; a₁) = ∑ ω, μ(ω) P(Pr | ω; a₁)`.
Source: [[corr-wf14-inventory]] 001 / filler.md R1; miri.md Dict-1 (`p(o; a₁)`)
Kind: D
Fidelity: exact -/
noncomputable def pressMass (a : A₁) : ℝ := ∑ ω, (S.μ a).mass ω * S.press a ω

/-- **Nondegeneracy** at `a₁`: `0 < P(Pr; a₁) < 1` — both conditional forms are defined. A name
of record offered to dependents: the conditional-form lemmas below take the half they need
(`0 < pressMass` or `pressMass < 1`) directly, and `thresholdIneqs_iff_condExp_of_nondegenerate`
routes both through this predicate. A disabled button has `pressMass = 0` and violates it.
Source: [[corr-wf14-inventory]] 001 / filler.md R1
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
def Nondegenerate (a : A₁) : Prop := 0 < S.pressMass a ∧ S.pressMass a < 1

/-- The press mass is the press-weighted expectation of the constant `1`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pressMass_eq_obsExpect_one (a : A₁) : S.pressMass a = S.obsExpect a .press (fun _ => 1) := by
  simp [pressMass, obsExpect]

/-- The silence mass `1 − P(Pr; a₁)` is the silence-weighted expectation of the constant `1`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma one_sub_pressMass_eq_obsExpect_one (a : A₁) :
    1 - S.pressMass a = S.obsExpect a .silent (fun _ => 1) := by
  simp only [pressMass, obsExpect, obsWeight_silent, mul_one, mul_sub, sum_sub_distrib,
    (S.μ a).sum_eq_one]

/-- The press mass is nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pressMass_nonneg (a : A₁) : 0 ≤ S.pressMass a :=
  sum_nonneg fun ω _ => mul_nonneg ((S.μ a).nonneg ω) (S.press_nonneg a ω)

/-- The press mass is at most one. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pressMass_le_one (a : A₁) : S.pressMass a ≤ 1 := by
  calc S.pressMass a ≤ ∑ ω, (S.μ a).mass ω :=
        sum_le_sum fun ω _ => by
          have := (S.μ a).nonneg ω
          nlinarith [S.press_le_one a ω]
    _ = 1 := (S.μ a).sum_eq_one

/-- Each summand of the product-form expectation with a nonnegative integrand is nonnegative.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsExpect_nonneg (a : A₁) (o : Obs) {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) :
    0 ≤ S.obsExpect a o X :=
  sum_nonneg fun ω _ =>
    mul_nonneg (mul_nonneg ((S.μ a).nonneg ω) (S.obsWeight_nonneg a o ω)) (h ω)

/-- Monotonicity of the product-form expectation.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsExpect_mono (a : A₁) (o : Obs) {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) :
    S.obsExpect a o X ≤ S.obsExpect a o Y :=
  sum_le_sum fun ω _ =>
    mul_le_mul_of_nonneg_left (h ω) (mul_nonneg ((S.μ a).nonneg ω) (S.obsWeight_nonneg a o ω))

/-- Linearity: differences. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsExpect_sub (a : A₁) (o : Obs) (X Y : Ω → ℝ) :
    S.obsExpect a o (fun ω => X ω - Y ω) = S.obsExpect a o X - S.obsExpect a o Y := by
  simp only [obsExpect, mul_sub, sum_sub_distrib]

/-- Linearity: sums. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsExpect_add (a : A₁) (o : Obs) (X Y : Ω → ℝ) :
    S.obsExpect a o (fun ω => X ω + Y ω) = S.obsExpect a o X + S.obsExpect a o Y := by
  simp only [obsExpect, mul_add, sum_add_distrib]

/-- Linearity: scalars. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsExpect_const_mul (a : A₁) (o : Obs) (k : ℝ) (X : Ω → ℝ) :
    S.obsExpect a o (fun ω => k * X ω) = k * S.obsExpect a o X := by
  simp only [obsExpect, mul_sum]
  exact sum_congr rfl fun ω _ => by ring

/-- Linearity: negation. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsExpect_neg (a : A₁) (o : Obs) (X : Ω → ℝ) :
    S.obsExpect a o (fun ω => -X ω) = -S.obsExpect a o X := by
  simp only [obsExpect, mul_neg, sum_neg_distrib]

/-- **Tower property**: the press and silence halves of a variable sum to its prior expectation,
`E_P[X 1_Pr] + E_P[X 1_¬Pr] = E_μ[X]`.
Source: [[corr-wf14-inventory]] 003 / filler.md F2(iii) ("by the tower property")
Kind: L
Fidelity: exact
Hyps: (a) only -/
lemma obsExpect_press_add_silent (a : A₁) (X : Ω → ℝ) :
    S.obsExpect a .press X + S.obsExpect a .silent X = expect (S.μ a) X := by
  simp only [obsExpect, expect, obsWeight_press, obsWeight_silent, ← sum_add_distrib]
  exact sum_congr rfl fun ω _ => by ring

/-- When the press has mass zero every press-weighted expectation vanishes (each summand
`μ(ω) P(Pr|ω)` is zero). This is the mechanism behind "after a null press every action is
posterior-optimal".
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsExpect_press_eq_zero_of_pressMass_eq_zero (a : A₁) (h : S.pressMass a = 0) (X : Ω → ℝ) :
    S.obsExpect a .press X = 0 := by
  have hterm : ∀ ω ∈ (univ : Finset Ω), (S.μ a).mass ω * S.press a ω = 0 :=
    (sum_eq_zero_iff_of_nonneg fun ω _ =>
      mul_nonneg ((S.μ a).nonneg ω) (S.press_nonneg a ω)).mp h
  simp only [obsExpect, obsWeight_press]
  exact sum_eq_zero fun ω hω => by rw [hterm ω hω, zero_mul]

/-- The joint expectation `E_P[f(o, ω); a₁] = ∑ ω, μ(ω) (P(Pr|ω) f(Pr, ω) + P(¬Pr|ω) f(¬Pr, ω))`
of a policy's payoff `f : Obs → Ω → ℝ`.
Source: [[corr-wf14-inventory]] 001 / filler.md R1 (`E_P[· ; a₁]`); miri.md Dict-2
Kind: D
Fidelity: exact -/
noncomputable def jointExpect (a : A₁) (f : Obs → Ω → ℝ) : ℝ :=
  ∑ ω, (S.μ a).mass ω * (S.press a ω * f .press ω + (1 - S.press a ω) * f .silent ω)

/-- The joint expectation splits into the two product-form halves.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma jointExpect_eq (a : A₁) (f : Obs → Ω → ℝ) :
    S.jointExpect a f = S.obsExpect a .press (f .press) + S.obsExpect a .silent (f .silent) := by
  simp only [jointExpect, obsExpect, obsWeight_press, obsWeight_silent, ← sum_add_distrib]
  exact sum_congr rfl fun ω _ => by ring
/-! ## The predicates of record (product form, named by the inequality) -/

/-- **The below-threshold inequality** on `X` at `a₁`: `E_P[X · 1_Pr ; a₁] ≤ 0`, i.e.
`∑ ω, μ(ω) P(Pr|ω;a₁) X(ω) ≤ 0` — `E_P[X | Pr; a₁] ≤ 0` multiplied by the press mass. The
corpus calls it the below-threshold Total Trust inequality at threshold `0`; at `pressMass = 0`
it is vacuously true (both sides `0`), so its content lives at `0 < pressMass`.
Source: [[corr-wf13-inventory]] 001 / position statement §2.9; miri.md Dict-4; filler.md F1
Kind: D
Fidelity: exact (denominator-free form, rigor critique 11)
Hyps: n/a (definition) -/
def belowThresholdIneq (a : A₁) (X : Ω → ℝ) : Prop := S.obsExpect a .press X ≤ 0

/-- **The above-threshold inequality** on `X` at `a₁`: `0 ≤ E_P[X · 1_¬Pr ; a₁]`, i.e.
`0 ≤ ∑ ω, μ(ω) (1 − P(Pr|ω;a₁)) X(ω)` — `E_P[X | ¬Pr; a₁] ≥ 0` times the silence mass. The
*weak* form (`0 ≤`) is chosen, following filler.md F2(ii) and mm.md I13.4 as the mandate specified;
`miri.md` Dict-4's above-threshold clause is strict (`E_P[X | o; a₁] > 0` for every non-press `o`
of positive mass), whose two-option form is `0 < Δ₊` (witnessed by `Witnesses.w3_both_strict`).
At `pressMass = 1` (a press in every world) it is vacuously true (both sides `0`) and `Δ₊ = 0`,
the silence-side twin of `belowThresholdIneq`'s vacuity at `pressMass = 0`
(`Witnesses.twoState_aboveThresholdIneq_of_press_one`); its content lives at `pressMass < 1`.
Source: [[corr-wf13-inventory]] 001 / position statement §2.9 ("the above-threshold twin"); miri.md Dict-4 (strict there)
Kind: D
Fidelity: exact (denominator-free)
Hyps: n/a (definition) -/
def aboveThresholdIneq (a : A₁) (X : Ω → ℝ) : Prop := 0 ≤ S.obsExpect a .silent X

/-- The *derived* conditional expectation `E_P[X | Pr; a₁] = E_P[X 1_Pr] / P(Pr)`. Lean's
`x / 0 = 0` makes it `0` at `pressMass = 0`; no headline rests on that value — every `↔` to
the product form carries `0 < pressMass` explicitly.
Source: [[corr-wf14-inventory]] 001 / filler.md R1; miri.md Dict-3
Kind: D
Fidelity: exact under `0 < pressMass` -/
noncomputable def condExpPress (a : A₁) (X : Ω → ℝ) : ℝ := S.obsExpect a .press X / S.pressMass a

/-- The derived `E_P[X | ¬Pr; a₁] = E_P[X 1_¬Pr] / (1 − P(Pr))`; junk at `pressMass = 1`.
Source: [[corr-wf14-inventory]] 001 / filler.md R1
Kind: D
Fidelity: exact under `pressMass < 1` -/
noncomputable def condExpSilent (a : A₁) (X : Ω → ℝ) : ℝ :=
  S.obsExpect a .silent X / (1 - S.pressMass a)

/-- The derived posterior mass `P(ω | Pr; a₁) = μ(ω) P(Pr|ω;a₁) / P(Pr;a₁)` after a press.
Source: miri.md Dict-1 ("the posterior is … when `p(o; a₁) > 0`")
Kind: D
Fidelity: exact under `0 < pressMass` -/
noncomputable def posteriorPress (a : A₁) (ω : Ω) : ℝ :=
  (S.μ a).mass ω * S.press a ω / S.pressMass a

/-- The conditional expectation is the posterior-weighted sum (an identity of rational
expressions; holds with junk values too, `0 = ∑ 0`).
Source: miri.md Dict-2
Kind: L
Fidelity: exact -/
lemma condExpPress_eq_sum_posterior (a : A₁) (X : Ω → ℝ) :
    S.condExpPress a X = ∑ ω, S.posteriorPress a ω * X ω := by
  simp only [condExpPress, obsExpect, obsWeight_press, posteriorPress, sum_div]
  exact sum_congr rfl fun ω _ => by ring

/-- Under nondegeneracy the below-threshold inequality is exactly `E_P[X | Pr; a₁] ≤ 0`.
Source: [[corr-wf14-inventory]] 001 / filler.md F1 (the "multiply by `p(Pr)`" step)
Kind: L
Fidelity: exact -/
lemma belowThresholdIneq_iff_condExpPress (a : A₁) (X : Ω → ℝ) (h : 0 < S.pressMass a) :
    S.belowThresholdIneq a X ↔ S.condExpPress a X ≤ 0 := by
  unfold belowThresholdIneq condExpPress
  rw [div_le_iff₀ h, zero_mul]

/-- Under `pressMass < 1` the above-threshold inequality is exactly `0 ≤ E_P[X | ¬Pr; a₁]`.
Source: [[corr-wf14-inventory]] 001 / filler.md F2(ii)
Kind: L
Fidelity: exact -/
lemma aboveThresholdIneq_iff_condExpSilent (a : A₁) (X : Ω → ℝ) (h : S.pressMass a < 1) :
    S.aboveThresholdIneq a X ↔ 0 ≤ S.condExpSilent a X := by
  unfold aboveThresholdIneq condExpSilent
  rw [le_div_iff₀ (by linarith), zero_mul]

/-- Under nondegeneracy, both conditional forms at once: the below-threshold inequality on `X` is
`E_P[X | Pr; a₁] ≤ 0` and the above-threshold inequality on `Y` is `0 ≤ E_P[Y | ¬Pr; a₁]` — the
route through `Nondegenerate` for dependents that carry the predicate rather than its halves.
Source: [[corr-wf14-inventory]] 001 / filler.md R1, F1, F2(ii)
Kind: L
Fidelity: exact -/
lemma thresholdIneqs_iff_condExp_of_nondegenerate (a : A₁) (X Y : Ω → ℝ) (h : S.Nondegenerate a) :
    (S.belowThresholdIneq a X ↔ S.condExpPress a X ≤ 0) ∧
      (S.aboveThresholdIneq a Y ↔ 0 ≤ S.condExpSilent a Y) :=
  ⟨S.belowThresholdIneq_iff_condExpPress a X h.1, S.aboveThresholdIneq_iff_condExpSilent a Y h.2⟩

/-! ## Posterior optimality, part-maximisers, desideratum 1 -/

/-- `b` is **posterior-optimal** at `(a₁, o)`: no `b'` has larger `E_P[V(a₁,o,b',·) 1_o ; a₁]`.
Product form: equivalent to `argmax E_P[V | o; a₁]` when the observation has positive mass,
and *vacuously true for every `b`* when it has mass zero (after a null press every action is
posterior-optimal) — the reason nondegeneracy exists as a hypothesis.
Source: [[corr-wf13-inventory]] 001 / miri.md Dict-2 (`A₂^T`); position statement §2.8
Kind: D
Fidelity: exact -/
def PosteriorOptimalAt (a : A₁) (o : Obs) (b : A₂) : Prop :=
  ∀ b' : A₂, S.obsExpect a o (S.V a o b') ≤ S.obsExpect a o (S.V a o b)

/-- After a press of mass zero every action is posterior-optimal (in product form).
Source: [[corr-wf14-inventory]] 001 / filler.md R1 (the nondegeneracy remark)
Kind: L
Fidelity: exact -/
lemma posteriorOptimalAt_press_of_pressMass_eq_zero (a : A₁) (h : S.pressMass a = 0) (b : A₂) :
    S.PosteriorOptimalAt a .press b := fun b' => by
  rw [S.obsExpect_press_eq_zero_of_pressMass_eq_zero a h,
    S.obsExpect_press_eq_zero_of_pressMass_eq_zero a h]

/-- `b` is a **part-maximiser** of `T ⊆ A₂` at `(a₁, o)`: `b ∈ T` and `o`-weighted-optimal within
`T`. The sources' `a₂^cont ∈ argmax_{A₂^c}` and `a₂^sh ∈ argmax_{Sh}`; theorems quantify over
every such `b`, never over a chosen one.
Source: [[corr-wf14-inventory]] 001 / filler.md R1; miri.md Dict-3
Kind: D
Fidelity: exact -/
def IsPartBest (a : A₁) (o : Obs) (T : Finset A₂) (b : A₂) : Prop :=
  b ∈ T ∧ ∀ b' ∈ T, S.obsExpect a o (S.V a o b') ≤ S.obsExpect a o (S.V a o b)

/-- Every nonempty part has a part-maximiser (finite maximum).
Source: [[corr-wf14-inventory]] 002 / filler.md F1 ("plus existence of such a pair")
Kind: L
Fidelity: exact -/
lemma exists_isPartBest (a : A₁) (o : Obs) {T : Finset A₂} (hT : T.Nonempty) :
    ∃ b, S.IsPartBest a o T b :=
  let ⟨b, hb, hmax⟩ := T.exists_max_image (fun b => S.obsExpect a o (S.V a o b)) hT
  ⟨b, hb, hmax⟩

/-- **Desideratum 1 at `a₁`**: some shutdown action is posterior-optimal after a press —
"shuts down means `A₂(a₁, Pr) ∈ Sh` is posterior-optimal" (position statement §2.8).
Source: [[corr-wf13-inventory]] 001 / position statement §2.8; miri.md Dict-3
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
def D1At (a : A₁) : Prop := ∃ b ∈ S.Sh, S.PosteriorOptimalAt a .press b

/-! ## The two-option variables -/

/-- The two-option variable `X_o(ω) = V(a₁, o, c, ω) − V(a₁, o, s, ω)`: the value of continuing
with `c` over stopping with `s`, indexed by the observation exactly as the sources' `X_o`.
Source: [[corr-wf14-inventory]] 001 / filler.md R1; miri.md Dict-3
Kind: D
Fidelity: exact -/
def Xo (a : A₁) (o : Obs) (c s : A₂) : Ω → ℝ := fun ω => S.V a o c ω - S.V a o s ω

/-- `Δ₋(a₁) = −E_P[X_Pr · 1_Pr ; a₁]`: minus the press half of the two-option variable.
Source: [[corr-wf14-inventory]] 003 / filler.md F2
Kind: D
Fidelity: exact -/
noncomputable def deltaMinus (a : A₁) (c s : A₂) : ℝ := -(S.obsExpect a .press (S.Xo a .press c s))

/-- `Δ₊(a₁) = E_P[X_¬Pr · 1_¬Pr ; a₁]`: the silence half of the two-option variable.
Source: [[corr-wf14-inventory]] 003 / filler.md F2
Kind: D
Fidelity: exact -/
noncomputable def deltaPlus (a : A₁) (c s : A₂) : ℝ := S.obsExpect a .silent (S.Xo a .silent c s)

/-- The off-switch game's `Δ = min(Δ₋, Δ₊)`.
Source: [[corr-wf14-inventory]] 003 / filler.md F2; Hadfield-Menell et al. 2017 Eq. 1
Kind: D
Fidelity: exact -/
noncomputable def delta (a : A₁) (c s : A₂) : ℝ := min (S.deltaMinus a c s) (S.deltaPlus a c s)

/-- The programmers' recommended strategy `S^H`: stop with `s` on a press, continue with `c`
on silence, as a payoff `Obs → Ω → ℝ`.
Source: [[corr-wf14-inventory]] 003 / filler.md F2
Kind: D
Fidelity: exact -/
def shPolicy (a : A₁) (c s : A₂) : Obs → Ω → ℝ :=
  fun o ω => if o = .press then S.V a o s ω else S.V a o c ω

/-- The constant strategy "play `b` whatever is observed", as a payoff.
Source: [[corr-wf14-inventory]] 003 / filler.md F2 (`V(c)`, `V(s)`)
Kind: D
Fidelity: exact -/
def constPolicy (a : A₁) (b : A₂) : Obs → Ω → ℝ := fun o ω => S.V a o b ω

/-- The **off-switch game's incentive** (Hadfield-Menell et al. 2017, Eq. 1):
`Δ = E[π^H(U) · U] − max{E[U], 0}`, with `π^H` the probability the human *allows* the action,
stated here on any finite prior with `π^H` any `[0,1]`-valued function of the world.
Source: Hadfield-Menell et al. 2017 Eq. 1 (`04-chai/hadfield-menell-2017-the-off-switch-game.md` l. 88–102)
Kind: D
Fidelity: variant: `π^H` is a function of `ω`; the paper's `π^H : ℝ → [0,1]` of `U_a` alone is the special case `π^H ω = g (U ω)` -/
noncomputable def osgDelta {Ω' : Type*} [Fintype Ω'] (μ : Distr Ω') (U πH : Ω' → ℝ) : ℝ :=
  expect μ (fun ω => πH ω * U ω) - max (expect μ U) 0

/-! ## Value-of-information objects -/

include S in
/-- `A₂` is nonempty (it contains `Sh`). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma univ_nonempty : (univ : Finset A₂).Nonempty := by
  obtain ⟨b, -⟩ := S.Sh_nonempty
  exact ⟨b, mem_univ b⟩

/-- The prior value `E_μ[V(a₁, o₀, b, ·)]` of the final action `b` (the observation index
`o₀` is immaterial under A1).
Source: [[corr-wf14-inventory]] 005 / filler.md F4(b) (`max_{a₂} E_P[V]`)
Kind: D
Fidelity: exact -/
noncomputable def priorValue (a : A₁) (o₀ : Obs) (b : A₂) : ℝ := expect (S.μ a) (S.V a o₀ b)

/-- `max_{b ∈ A₂} E_P[V(a₁,o,b,·) · 1_o ; a₁]`: the `o`-weighted value of the best response
to `o` (the summand of `E_o[max_{a₂} E_P[V | o]]`, event mass included).
Source: [[corr-wf14-inventory]] 005 / filler.md F4(b); miri.md Prop. 10.5
Kind: D
Fidelity: exact -/
noncomputable def obsMax (a : A₁) (o : Obs) : ℝ :=
  univ.sup' S.univ_nonempty (fun b => S.obsExpect a o (S.V a o b))

/-- `max_{b ∈ A₂} E_μ[V(a₁, o₀, b, ·)]`, the value of the best prior action.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(b)
Kind: D
Fidelity: exact -/
noncomputable def priorMax (a : A₁) (o₀ : Obs) : ℝ :=
  univ.sup' S.univ_nonempty (fun b => S.priorValue a o₀ b)

/-- **The value of the button** `VOI(a₁) = E_o[max_{a₂} E_P[V | o]] − max_{a₂} E_P[V]` on the full
menu `A₂`, in product form: the press-weighted max plus the silence-weighted max, minus the
prior max. No division; no regime assumption built in.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(b); miri.md Prop. 10.5
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def voiButton (a : A₁) (o₀ : Obs) : ℝ :=
  S.obsMax a .press + S.obsMax a .silent - S.priorMax a o₀

/-- The informed agent's value on the two-option menu `{c, s}`: best response to the press
plus best response to silence, each weighted by its event mass.
Source: [[corr-wf14-inventory]] 005 / filler.md F4 (two-option menu)
Kind: D
Fidelity: exact -/
noncomputable def twoOptionValue (a : A₁) (c s : A₂) : ℝ :=
  max (S.obsExpect a .press (S.V a .press c)) (S.obsExpect a .press (S.V a .press s)) +
    max (S.obsExpect a .silent (S.V a .silent c)) (S.obsExpect a .silent (S.V a .silent s))

/-- The value of a **hard button** on the menu `{c, s}`: a press *forces* `s`; on silence the
agent plays its best response among `{c, s}`.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(a) (`a₁^dir`)
Kind: D
Fidelity: variant: the forcing is modelled as this value expression, not as a change to the agent's decision rule -/
noncomputable def hardButtonValue (a : A₁) (c s : A₂) : ℝ :=
  S.obsExpect a .press (S.V a .press s) +
    max (S.obsExpect a .silent (S.V a .silent c)) (S.obsExpect a .silent (S.V a .silent s))

/-- The prior value of the two-option menu: `max(E_μ[V(c)], E_μ[V(s)])`.
Source: [[corr-wf14-inventory]] 005 / filler.md F4
Kind: D
Fidelity: exact -/
noncomputable def twoOptionPriorValue (a : A₁) (o₀ : Obs) (c s : A₂) : ℝ :=
  max (S.priorValue a o₀ c) (S.priorValue a o₀ s)

/-- The value of the button on the two-option menu `{c, s}`.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(b)
Kind: D
Fidelity: exact -/
noncomputable def voiButton2 (a : A₁) (o₀ : Obs) (c s : A₂) : ℝ :=
  S.twoOptionValue a c s - S.twoOptionPriorValue a o₀ c s

end ThreeStep

/-! ## The canonical two-state instance -/

/-- The two-state value latent: the agent's plan is `right` or `wrong`.
Source: [[corr-wf13-inventory]] 003 / miri.md Dict-6 (C2)
Kind: D
Fidelity: exact -/
inductive World
  | right
  | wrong
  deriving DecidableEq

/-- `World` is finite, with `univ = {right, wrong}` definitionally.
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype World := ⟨{World.right, World.wrong}, fun x => by cases x <;> simp⟩

/-- Sums over `World` expand to two terms. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma World.sum_eq (f : World → ℝ) : ∑ ω, f ω = f .right + f .wrong := by
  rw [show (univ : Finset World) = {World.right, World.wrong} from rfl, sum_pair (by decide)]

/-- The two-option final menu: continue or stop.
Source: [[corr-wf13-inventory]] 003 / miri.md Dict-6
Kind: D
Fidelity: exact -/
inductive TwoAct
  | cont
  | stop
  deriving DecidableEq

/-- `TwoAct` is finite, with `univ = {cont, stop}` definitionally.
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype TwoAct := ⟨{TwoAct.cont, TwoAct.stop}, fun x => by cases x <;> simp⟩

/-- The two-point prior with `mass wrong = ε`, built directly as a FAF `Distr`.
Source: [[corr-wf13-inventory]] 003 / miri.md Dict-6 (`μ(W) = ε`)
Kind: D
Fidelity: exact -/
noncomputable def twoPoint (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) : Distr World where
  mass ω := match ω with
    | .right => 1 - ε
    | .wrong => ε
  nonneg ω := by cases ω <;> simp <;> linarith [hε.1, hε.2]
  sum_eq_one := by rw [World.sum_eq]; simp

/-- Mass of `right` under `twoPoint`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma twoPoint_right (ε : ℝ) (hε) : (twoPoint ε hε).mass .right = 1 - ε := rfl

/-- Mass of `wrong` under `twoPoint`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma twoPoint_wrong (ε : ℝ) (hε) : (twoPoint ε hε).mass .wrong = ε := rfl

/-- The press rate of the two-state sensor: `α` when right (false press), `β` when wrong.
Source: [[corr-wf13-inventory]] 003 / miri.md Dict-6
Kind: D
Fidelity: exact -/
def twoPress (α β : ℝ) : World → ℝ
  | .right => α
  | .wrong => β

/-- The two-state value: continuing is worth `c` when right and `−h` when wrong; stopping is
normalised to `0` (as in the off-switch game).
Source: [[corr-wf13-inventory]] 003 / miri.md Dict-6 (`X(R) = c`, `X(W) = −h`)
Kind: D
Fidelity: exact -/
def twoValue (c h : ℝ) : TwoAct → World → ℝ
  | .cont, .right => c
  | .cont, .wrong => -h
  | .stop, _ => 0

/-- **The canonical two-state instance** `C2` of Setting S: one first action, `Ω = World` with
`μ(wrong) = ε`, sensor `(α, β)`, menu `{cont, stop}` with `Sh = {stop}`, `V` as `twoValue`
(A1 holds by construction). Only the bounds needed for the objects to exist are taken here;
each theorem names the standing hypotheses (`0 < ε < 1`, `0 < β`, `0 < c`, `0 < h`, …) it uses.
Source: [[corr-wf13-inventory]] 003 / miri.md Dict-6; position statement §2.13(b)
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def twoState (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    ThreeStep World Unit TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => twoPoint ε hε
  press := fun _ => twoPress α β
  press_nonneg := fun _ ω => match ω with
    | .right => hα.1
    | .wrong => hβ.1
  press_le_one := fun _ ω => match ω with
    | .right => hα.2
    | .wrong => hβ.2
  V := fun _ _ => twoValue c h

/-- The **compliance threshold** `c / (c + h)`: the posterior probability of being wrong above
which stopping is posterior-optimal.
Source: [[corr-wf13-inventory]] 002 / position statement §2.13(a); miri.md I12.1
Kind: D
Fidelity: exact -/
noncomputable def complianceThreshold (c h : ℝ) : ℝ := c / (c + h)

/-- `ε* = α c / (α c + β h)`: the error rate at which desideratum 1 and the repair incentive
vanish together on the two-state instance.
Source: [[corr-wf13-inventory]] 004; [[corr-wf14b-inventory]] 033 / channel-final.md D13, P10
Kind: D
Fidelity: exact -/
noncomputable def epsStar (α β c h : ℝ) : ℝ := α * c / (α * c + β * h)

end Cleanroom.Found.CorrThreeStep
