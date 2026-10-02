import Cleanroom.Udt.UdtPolicyCalc.Newcomb
import Mathlib.Tactic.FieldSimp

/-!
# Transparent Newcomb with predictor error `ε`: T9, T10, T11

The model ([[gap1-reframing-predictor-access]] §8): observations `TObs = {full, empty}`, actions
`BoxAct = {one, two}`, four policies `mk af ae`; the predictor predicts the agent's *full-box*
action, correctly with probability `1 − ε` (a coin `c : Bool`, `true` = correct); the big box is
filled iff the prediction is `one`; the agent observes the box and acts by `π`; payoff
`u (o, a)`: `(full, one) = 10⁶`, `(full, two) = 1001000`, `(empty, one) = 0`, `(empty, two) = 1000`.
`V ε π` is the expectation over the coin, **derived** from the model, not a table.

* T9: the four closed forms, `V_oneTwo_sub_twoTwo`, `isOptimal_oneTwo_iff` (threshold
  `999/1999`, exact rational), `oneTwo_strictArgmax` (uniqueness for `<`).
* T10: the joint law over `(policy, coin)` with a **prior `μ` over the agent's own policy**;
  the EDT rule `edtScore` (condition on observation and action, junk `-1`);
  (a) `edt_ne_udt_transparent` — the separation, **on the full branch**;
  (b) `separation_vanishes_of_null_event`, `edt_rule_oneBoxes_on_full_of_eps_zero` — the junk-value
  collapse at `ε = 0` / null prior; (c) `ctScore` (the C&T rule: condition on `Π o = a` under
  the prior, no observation) with `ctRule_oneBoxes_on_full_of_lt` (threshold `999/2000`) and
  `ctRule_disagrees_with_udt11_on_empty`; (d) `condProb_empty_given_full_one` (`= ε`) and
  `condProb_empty_given_full_two` (`= 1 − ε`).
* T11 is a docstring sentence on `isOptimal_oneTwo_iff`.

Package `udt-policy-calc` (faf-cleanroom run, 2026-09-29).
-/

namespace Cleanroom.Udt.UdtPolicyCalc

noncomputable section

namespace Transparent

open Finset

/-- Supporting lemma `one_eq_two_iff` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem one_eq_two_iff : (BoxAct.one = BoxAct.two) ↔ False := by simp
/-- Supporting lemma `two_eq_one_iff` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem two_eq_one_iff : (BoxAct.two = BoxAct.one) ↔ False := by simp

/-- The two observations: the big box is seen full or empty.
Source: [[gap1-reframing-predictor-access]] §8 (udt-rep-034)
Kind: D
Fidelity: exact
Hyps: n/a -/
inductive TObs
  | full
  | empty
  deriving DecidableEq, Fintype

/-- Policies of the transparent problem.
Source: [[gap1-reframing-predictor-access]] §8 (udt-rep-034)
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev TPolicy := Policy TObs BoxAct

/-- The policy `(full ↦ af, empty ↦ ae)`.
Source: [[gap1-reframing-predictor-access]] §8 ("Policy (full, empty)")
Kind: D
Fidelity: exact
Hyps: n/a -/
def mk (af ae : BoxAct) : TPolicy := fun o =>
  match o with
  | .full => af
  | .empty => ae

/-- Supporting lemma `mk_full` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem mk_full (af ae : BoxAct) : mk af ae TObs.full = af := rfl
/-- Supporting lemma `mk_empty` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem mk_empty (af ae : BoxAct) : mk af ae TObs.empty = ae := rfl

/-- Supporting lemma `policy_eq_mk` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem policy_eq_mk (π : TPolicy) : π = mk (π TObs.full) (π TObs.empty) := by
  funext o
  cases o <;> rfl

/-- Supporting lemma `mk_inj` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mk_inj {af ae af' ae' : BoxAct} : mk af ae = mk af' ae' ↔ af = af' ∧ ae = ae' :=
  ⟨fun h => ⟨congrFun h TObs.full, congrFun h TObs.empty⟩, by
    rintro ⟨rfl, rfl⟩
    rfl⟩

/-- Quantification over the four policies.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem forall_tpolicy {P : TPolicy → Prop} :
    (∀ π, P π) ↔ P (mk .one .one) ∧ P (mk .one .two) ∧ P (mk .two .one) ∧ P (mk .two .two) := by
  constructor
  · intro h
    exact ⟨h _, h _, h _, h _⟩
  · rintro ⟨h11, h12, h21, h22⟩ π
    rw [policy_eq_mk π]
    rcases hf : π TObs.full with _ | _ <;> rcases he : π TObs.empty with _ | _ <;> assumption

/-- The policies as pairs of actions.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def mkEquiv : BoxAct × BoxAct ≃ TPolicy where
  toFun p := mk p.1 p.2
  invFun π := (π TObs.full, π TObs.empty)
  left_inv p := rfl
  right_inv π := (policy_eq_mk π).symm

/-- A sum over the four policies, expanded.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem tpolicy_sum {M : Type} [AddCommMonoid M] (g : TPolicy → M) :
    ∑ π, g π = g (mk .one .one) + g (mk .one .two) + g (mk .two .one) + g (mk .two .two) := by
  rw [← mkEquiv.sum_comp g, Fintype.sum_prod_type]
  simp only [BoxAct.sum_eq, mkEquiv, Equiv.coe_fn_mk, add_assoc]

/-- The other action.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def flip : BoxAct → BoxAct
  | .one => .two
  | .two => .one

/-- The predictor's prediction of the agent's full-box action: correct when the coin is `true`.
Source: [[gap1-reframing-predictor-access]] §8 ("the predictor errs with probability ε")
Kind: D
Fidelity: exact
Hyps: n/a -/
def prediction (π : TPolicy) (c : Bool) : BoxAct := if c then π TObs.full else flip (π TObs.full)

/-- The box the agent sees: full iff the prediction is `one`.
Source: [[gap1-reframing-predictor-access]] §8
Kind: D
Fidelity: exact
Hyps: n/a -/
def obs (π : TPolicy) (c : Bool) : TObs := if prediction π c = BoxAct.one then TObs.full else TObs.empty

/-- The agent's action: its policy applied to what it sees.
Source: [[gap1-reframing-predictor-access]] §8
Kind: D
Fidelity: exact
Hyps: n/a -/
def act (π : TPolicy) (c : Bool) : BoxAct := π (obs π c)

/-- The payoff table `u (o, a)`.
Source: [[gap1-reframing-predictor-access]] §8 (small box \$1K, big box \$1M)
Kind: D
Fidelity: exact
Hyps: n/a -/
def u : TObs → BoxAct → ℝ
  | .full, .one => 1000000
  | .full, .two => 1001000
  | .empty, .one => 0
  | .empty, .two => 1000

/-- The realized payoff of `π` under coin `c`.
Source: [[gap1-reframing-predictor-access]] §8
Kind: D
Fidelity: exact
Hyps: n/a -/
def payoff (π : TPolicy) (c : Bool) : ℝ := u (obs π c) (act π c)

/-- The coin's weights: `1 − ε` on `true` (correct prediction), `ε` on `false`.
Source: [[gap1-reframing-predictor-access]] §8
Kind: D
Fidelity: exact
Hyps: n/a -/
def coinW (ε : ℝ) : Bool → ℝ := fun c => if c then 1 - ε else ε

/-- The coin as a `FinDist` (for `0 ≤ ε ≤ 1`).
Source: [[gap1-reframing-predictor-access]] §8
Kind: D
Fidelity: exact
Hyps: n/a -/
def coin (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : FinDist Bool where
  w := coinW ε
  nonneg c := by
    cases c <;> simp [coinW] <;> linarith
  sum_one := by simp [Fintype.sum_bool, coinW]

/-- **The policy value** `V ε π`: the expected payoff over the predictor's coin, derived from the
model (`payoff` under `coinW`), not a hand-written table.
Source: [[gap1-reframing-predictor-access]] §8 (udt-rep-034)
Kind: D
Fidelity: exact
Hyps: n/a -/
def V (ε : ℝ) (π : TPolicy) : ℝ := ∑ c : Bool, coinW ε c * payoff π c

/-- Supporting lemma `V_eq_exp` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem V_eq_exp (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (π : TPolicy) :
    V ε π = (coin ε h0 h1).exp (payoff π) := rfl

/-- **T9.** `V ε (one, two) = (1 − ε)·10⁶ + ε·10³`.
Source: [[gap1-reframing-predictor-access]] §8 table (udt-rep-034)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem V_oneTwo (ε : ℝ) : V ε (mk .one .two) = (1 - ε) * 1000000 + ε * 1000 := by
  simp [V, Fintype.sum_bool, coinW, payoff, obs, act, prediction, flip, u]

/-- **T9.** `V ε (two, two) = (1 − ε)·10³ + ε·1001000`.
Source: [[gap1-reframing-predictor-access]] §8 table (udt-rep-034)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem V_twoTwo (ε : ℝ) : V ε (mk .two .two) = (1 - ε) * 1000 + ε * 1001000 := by
  simp [V, Fintype.sum_bool, coinW, payoff, obs, act, prediction, flip, u]

/-- **T9.** `V ε (one, one) = (1 − ε)·10⁶`.
Source: [[gap1-reframing-predictor-access]] §8 table (udt-rep-034)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem V_oneOne (ε : ℝ) : V ε (mk .one .one) = (1 - ε) * 1000000 := by
  simp [V, Fintype.sum_bool, coinW, payoff, obs, act, prediction, flip, u]

/-- **T9.** `V ε (two, one) = ε·1001000`.
Source: [[gap1-reframing-predictor-access]] §8 table (udt-rep-034)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem V_twoOne (ε : ℝ) : V ε (mk .two .one) = ε * 1001000 := by
  simp [V, Fintype.sum_bool, coinW, payoff, obs, act, prediction, flip, u]

/-- **T9.** `V ε (one,two) − V ε (two,two) = 999000·(1−ε) − 10⁶·ε`.
Source: [[gap1-reframing-predictor-access]] §8 ("beats (2box, 2box) iff 999(1−ε) > 1000ε") (udt-rep-034)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem V_oneTwo_sub_twoTwo (ε : ℝ) :
    V ε (mk .one .two) - V ε (mk .two .two) = 999000 * (1 - ε) - 1000000 * ε := by
  rw [V_oneTwo, V_twoTwo]
  ring

/-- **T9, headline (udt-rep-034; T11(b)).** For `0 ≤ ε ≤ 1`, the policy `(one, two)` is optimal
iff `ε ≤ 999/1999` (exact rational). Read as "why ain't'cha rich" (udt-rep-2-006(b)): the UDT
policy is ex-ante richest iff the predictor's error is below `999/1999`. (Against `(one,one)` the
margin is `ε·10³ ≥ 0`; against `(two,one)` it is `10⁶ − 2·10⁶·ε`, positive for `ε < 1/2`.)
Source: [[gap1-reframing-predictor-access]] §8 ("π* dominates … iff ε < 999/1999") (udt-rep-034, 2-006(b))
Kind: P
Fidelity: exact (non-strict form of the source's strict threshold; ties allowed in `IsOptimal`)
Hyps: (a) `0 ≤ ε ≤ 1` (the coin is a distribution) -/
theorem isOptimal_oneTwo_iff {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    IsOptimal (V ε) (mk .one .two) ↔ ε ≤ 999 / 1999 := by
  constructor
  · intro h
    have := h (mk .two .two)
    rw [V_oneTwo, V_twoTwo] at this
    linarith
  · intro hε
    rw [IsOptimal, forall_tpolicy]
    simp only [V_oneOne, V_oneTwo, V_twoOne, V_twoTwo]
    refine ⟨?_, le_rfl, ?_, ?_⟩ <;> linarith

/-- **T9, uniqueness.** For `0 < ε < 999/1999`, `(one, two)` is the *strict* argmax of `V ε`.
Source: [[gap1-reframing-predictor-access]] §8 (udt-rep-034)
Kind: P
Fidelity: exact
Hyps: (a) `0 < ε` (else `(one,one)` ties), `ε < 999/1999` -/
theorem oneTwo_strictArgmax {ε : ℝ} (h0 : 0 < ε) (hε : ε < 999 / 1999) :
    IsStrictArgmax (V ε) (mk .one .two) := by
  intro π' hne
  have hπ' := policy_eq_mk π'
  rcases hf : π' TObs.full with _ | _ <;> rcases he : π' TObs.empty with _ | _ <;>
    rw [hf, he] at hπ' <;> subst hπ'
  · rw [V_oneOne, V_oneTwo]
    linarith
  · exact absurd rfl hne
  · rw [V_twoOne, V_oneTwo]
    linarith
  · rw [V_twoTwo, V_oneTwo]
    linarith

/-! ### T10: the joint law with a prior over the agent's own policy -/

/-- The joint weight of `(policy, coin)`: `μ π · coinW ε c`. The prior `μ` over the agent's
*own policy* is the object the corpus never made explicit (udt-rep-048).
Source: mandate T10 (udt-rep-048)
Kind: D
Fidelity: exact
Hyps: n/a -/
def jointW (μ : FinDist TPolicy) (ε : ℝ) : TPolicy × Bool → ℝ := fun ω => μ.w ω.1 * coinW ε ω.2

/-- Supporting lemma `jointW_nonneg` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem jointW_nonneg (μ : FinDist TPolicy) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (ω : TPolicy × Bool) :
    0 ≤ jointW μ ε ω :=
  mul_nonneg (μ.nonneg _) ((coin ε h0 h1).nonneg _)

/-- Supporting lemma `coinW_sum` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem coinW_sum (ε : ℝ) : ∑ c : Bool, coinW ε c = 1 := by simp [Fintype.sum_bool, coinW]

/-- Supporting lemma `jointW_sum_one` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem jointW_sum_one (μ : FinDist TPolicy) (ε : ℝ) : ∑ ω, jointW μ ε ω = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [jointW, ← Finset.mul_sum, coinW_sum, mul_one]
  exact μ.sum_one

/-- The joint law as a `FinDist`.
Source: mandate T10
Kind: D
Fidelity: exact
Hyps: n/a -/
def joint (μ : FinDist TPolicy) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : FinDist (TPolicy × Bool) :=
  ⟨jointW μ ε, jointW_nonneg μ h0 h1, jointW_sum_one μ ε⟩

/-- The observation, action and payoff as functions on the joint carrier.
Source: mandate T10
Kind: D
Fidelity: exact
Hyps: n/a -/
def obsΩ (ω : TPolicy × Bool) : TObs := obs ω.1 ω.2

/-- Supporting definition `actΩ` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: none -/
def actΩ (ω : TPolicy × Bool) : BoxAct := act ω.1 ω.2

/-- Supporting definition `payoffΩ` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: none -/
def payoffΩ (ω : TPolicy × Bool) : ℝ := payoff ω.1 ω.2

/-- **The EDT rule** at observation `o`: `E[U | O = o ∧ A = a]` under the joint, with the C&T junk
value `-1` on null events ([[notation]] §3.3's `E[U | a]`, conditioned also on the observation as
[[when-udt-edt-diverge]] line 21 says: "I am at `s` and I take action `a`").
Source: [[when-udt-edt-diverge]] lines 19–21; [[notation]] §3.3; [[communication-trust-translated]] line 269 (udt-rep-048, 090)
Kind: D
Fidelity: exact
Hyps: n/a -/
def edtScore (μ : FinDist TPolicy) (ε : ℝ) (o : TObs) (a : BoxAct) : ℝ :=
  condExpJunk (jointW μ ε) payoffΩ (event fun ω => obsΩ ω = o ∧ actΩ ω = a) (-1)

/-- On the event `{O = o, A = a}` the payoff is the constant `u o a`, so the EDT score is `u o a`
whenever the event has positive mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem edtScore_eq_of_pos {μ : FinDist TPolicy} {ε : ℝ} {o : TObs} {a : BoxAct}
    (h : 0 < mass (jointW μ ε) (event fun ω => obsΩ ω = o ∧ actΩ ω = a)) :
    edtScore μ ε o a = u o a := by
  apply condExpJunk_const_on _ h
  intro ω hω
  rw [mem_event] at hω
  simp only [payoffΩ, payoff]
  rw [← hω.1, ← hω.2]
  rfl

/-- Supporting lemma `mass_full_one_pos` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_full_one_pos {μ : FinDist TPolicy} {ε : ℝ} (hμ : ∀ π, 0 < μ.w π) (h0 : 0 ≤ ε)
    (h1 : ε < 1) : 0 < mass (jointW μ ε) (event fun ω => obsΩ ω = .full ∧ actΩ ω = .one) := by
  refine mass_pos_of_mem (jointW_nonneg μ h0 h1.le) (x₀ := (mk .one .one, true)) ?_ ?_
  · simp [obsΩ, actΩ, obs, act, prediction]
  · simp only [jointW, coinW, if_true]
    exact mul_pos (hμ _) (by linarith)

/-- Supporting lemma `mass_full_two_pos` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_full_two_pos {μ : FinDist TPolicy} {ε : ℝ} (hμ : ∀ π, 0 < μ.w π) (h0 : 0 < ε)
    (h1 : ε ≤ 1) : 0 < mass (jointW μ ε) (event fun ω => obsΩ ω = .full ∧ actΩ ω = .two) := by
  refine mass_pos_of_mem (jointW_nonneg μ h0.le h1) (x₀ := (mk .two .two, false)) ?_ ?_
  · simp [obsΩ, actΩ, obs, act, prediction, flip]
  · simp only [jointW, coinW, Bool.false_eq_true, if_false]
    exact mul_pos (hμ _) h0

/-- Supporting lemma `mass_empty_one_pos` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_empty_one_pos {μ : FinDist TPolicy} {ε : ℝ} (hμ : ∀ π, 0 < μ.w π) (h0 : 0 ≤ ε)
    (h1 : ε < 1) : 0 < mass (jointW μ ε) (event fun ω => obsΩ ω = .empty ∧ actΩ ω = .one) := by
  refine mass_pos_of_mem (jointW_nonneg μ h0 h1.le) (x₀ := (mk .two .one, true)) ?_ ?_
  · simp [obsΩ, actΩ, obs, act, prediction]
  · simp only [jointW, coinW, if_true]
    exact mul_pos (hμ _) (by linarith)

/-- Supporting lemma `mass_empty_two_pos` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_empty_two_pos {μ : FinDist TPolicy} {ε : ℝ} (hμ : ∀ π, 0 < μ.w π) (h0 : 0 ≤ ε)
    (h1 : ε < 1) : 0 < mass (jointW μ ε) (event fun ω => obsΩ ω = .empty ∧ actΩ ω = .two) := by
  refine mass_pos_of_mem (jointW_nonneg μ h0 h1.le) (x₀ := (mk .two .two, true)) ?_ ?_
  · simp [obsΩ, actΩ, obs, act, prediction]
  · simp only [jointW, coinW, if_true]
    exact mul_pos (hμ _) (by linarith)

/-- **T10(a).** For a full-support prior and `0 < ε < 1`, the EDT rule strictly prefers `two` at
`full`: `E[U | full, one] = 10⁶ < E[U | full, two] = 1001000` (both events positive:
`P(full, two) = μ{π full = two}·ε`, `P(full, one) = μ{π full = one}·(1−ε)`).
Source: [[when-udt-edt-diverge]] lines 84–88; [[daniel-h-challenge]] "Transparent Newcomb" (udt-rep-048)
Kind: P
Fidelity: exact
Hyps: (a) full-support prior (explicit), `0 < ε < 1` (explicit; both events non-null) -/
theorem edt_rule_twoBoxes_on_full_of_pos_support {μ : FinDist TPolicy} {ε : ℝ}
    (hμ : ∀ π, 0 < μ.w π) (h0 : 0 < ε) (h1 : ε < 1) :
    edtScore μ ε .full .one < edtScore μ ε .full .two := by
  rw [edtScore_eq_of_pos (mass_full_one_pos hμ h0.le h1),
    edtScore_eq_of_pos (mass_full_two_pos hμ h0 h1.le)]
  norm_num [u]

/-- **T10(a), empty branch.** At `empty` the EDT rule also two-boxes (`0 < 1000`) — as does the
UDT optimum: the corpus's empty-branch story does not separate the two rules.
Source: [[daniel-h-challenge]] "Transparent Newcomb" (udt-rep-048's flag)
Kind: P
Fidelity: exact
Hyps: (a) full-support prior, `0 ≤ ε < 1` -/
theorem edt_rule_twoBoxes_on_empty_of_pos_support {μ : FinDist TPolicy} {ε : ℝ}
    (hμ : ∀ π, 0 < μ.w π) (h0 : 0 ≤ ε) (h1 : ε < 1) :
    edtScore μ ε .empty .one < edtScore μ ε .empty .two := by
  rw [edtScore_eq_of_pos (mass_empty_one_pos hμ h0 h1),
    edtScore_eq_of_pos (mass_empty_two_pos hμ h0 h1)]
  norm_num [u]

/-- **T10(a), headline (udt-rep-048, load-bearing 1).** EDT ≠ UDT in transparent Newcomb, for every
full-support prior over the agent's own policy and every `0 < ε < 999/1999`: the EDT rule
strictly prefers `two` at both observations (so its policy is `(two, two)`), while the UDT1.1
optimum is uniquely `(one, two)`; **the divergence is on the full branch** (the corpus's prose
gives the empty-branch story, on which both two-box), and the ex-ante gap is
`V ε (one,two) − V ε (two,two) = 999000(1−ε) − 10⁶ε > 0`.
Source: [[when-udt-edt-diverge]] lines 84–88; [[daniel-h-challenge]]; `EDTvsUDT.lean` header ("not yet formalized") (udt-rep-048, 2-006(a), 2-031(b))
Kind: P
Fidelity: exact
Hyps: (a) full-support prior `μ` (explicit variable), `0 < ε < 999/1999` (explicit) -/
theorem edt_ne_udt_transparent {μ : FinDist TPolicy} {ε : ℝ} (hμ : ∀ π, 0 < μ.w π) (h0 : 0 < ε)
    (hε : ε < 999 / 1999) :
    (∀ o, IsStrictArgmax (edtScore μ ε o) .two) ∧ IsStrictArgmax (V ε) (mk .one .two) ∧
      mk .two .two TObs.full ≠ mk .one .two TObs.full ∧
        0 < V ε (mk .one .two) - V ε (mk .two .two) := by
  have h1 : ε < 1 := by linarith
  refine ⟨?_, oneTwo_strictArgmax h0 hε, by simp, ?_⟩
  · intro o a ha
    have ha' : a = .one := by cases a <;> simp_all
    subst ha'
    cases o
    · exact edt_rule_twoBoxes_on_full_of_pos_support hμ h0 h1
    · exact edt_rule_twoBoxes_on_empty_of_pos_support hμ h0.le h1
  · rw [V_oneTwo_sub_twoTwo]
    linarith

/-- The uniform prior over the four policies.
Source: mandate T10 witness
Kind: D
Fidelity: n/a
Hyps: n/a -/
def uniform : FinDist TPolicy where
  w _ := 1 / 4
  nonneg _ := by norm_num
  sum_one := by
    rw [tpolicy_sum]
    norm_num

/-- **T10(a), N+ witness.** At the uniform prior and `ε = 1/10` every event is positive and both
rules are non-constant: the hypothesis package of `edt_ne_udt_transparent` is inhabited.
Source: mandate T10 witness
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem edt_ne_udt_uniform_witness :
    edtScore uniform (1 / 10) .full .one = 1000000 ∧
      edtScore uniform (1 / 10) .full .two = 1001000 ∧
        edtScore uniform (1 / 10) .empty .one = 0 ∧
          edtScore uniform (1 / 10) .empty .two = 1000 ∧
            IsStrictArgmax (V (1 / 10)) (mk .one .two) := by
  have hμ : ∀ π, 0 < uniform.w π := fun _ => by norm_num [uniform]
  refine ⟨?_, ?_, ?_, ?_, oneTwo_strictArgmax (by norm_num) (by norm_num)⟩
  · rw [edtScore_eq_of_pos (mass_full_one_pos hμ (by norm_num) (by norm_num))]
    rfl
  · rw [edtScore_eq_of_pos (mass_full_two_pos hμ (by norm_num) (by norm_num))]
    rfl
  · rw [edtScore_eq_of_pos (mass_empty_one_pos hμ (by norm_num) (by norm_num))]
    rfl
  · rw [edtScore_eq_of_pos (mass_empty_two_pos hμ (by norm_num) (by norm_num))]
    rfl

/-! ### T10(b): the convention theorem -/

/-- If the event `{full, two}` is null, the EDT score of `two` at `full` is the junk value `-1`.
Source: [[communication-trust-translated]] line 269 (udt-rep-090); mandate T10(b)
Kind: P
Fidelity: exact
Hyps: (a) the null-event hypothesis (explicit) -/
theorem separation_vanishes_of_null_event {μ : FinDist TPolicy} {ε : ℝ}
    (h : mass (jointW μ ε) (event fun ω => obsΩ ω = .full ∧ actΩ ω = .two) = 0) :
    edtScore μ ε .full .two = -1 :=
  condExpJunk_of_mass_eq_zero h

/-- At `ε = 0` the event `{full, two}` is null: a two-boxer sees the full box only when the
predictor errs.
Source: mandate T10(b)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem mass_full_two_eq_zero_of_eps_zero (μ : FinDist TPolicy) :
    mass (jointW μ 0) (event fun ω => obsΩ ω = .full ∧ actΩ ω = .two) = 0 := by
  apply mass_eq_zero_of_forall
  rintro ⟨π, c⟩ hω
  rw [mem_event] at hω
  cases c
  · simp [jointW, coinW]
  · exfalso
    by_cases h : π TObs.full = .one
    · simp [obsΩ, actΩ, obs, act, prediction, h] at hω
    · simp [obsΩ, actΩ, obs, act, prediction, h] at hω

/-- If the prior gives no mass to policies two-boxing at `full`, the event `{full, two}` is null.
Source: mandate T10(b)
Kind: P
Fidelity: exact
Hyps: (a) none beyond the null-prior hypothesis -/
theorem mass_full_two_eq_zero_of_prior_null {μ : FinDist TPolicy} (ε : ℝ)
    (hμ : ∀ π, π TObs.full = .two → μ.w π = 0) :
    mass (jointW μ ε) (event fun ω => obsΩ ω = .full ∧ actΩ ω = .two) = 0 := by
  apply mass_eq_zero_of_forall
  rintro ⟨π, c⟩ hω
  rw [mem_event] at hω
  have hfull : π TObs.full = .two := by
    have h2 := hω.2
    simp only [actΩ, act] at h2
    simp only [obsΩ] at hω
    rw [hω.1] at h2
    exact h2
  simp [jointW, hμ π hfull]

/-- **T10(b), headline (udt-rep-090's convention).** At `ε = 0` with a full-support prior the EDT
rule "one-boxes" at `full`: `E[U | full, two] = -1 < 10⁶ = E[U | full, one]`. The separation is
convention-dependent under degenerate parameters; the `-1` convention makes every
probability-zero action strictly dispreferred. (With C&T's `[0,1]` payoffs and the earlier
draft's `j = 2`, the null action would instead be *preferred* — findings, no theorem.)
Source: [[communication-trust-translated]] lines 265–270 (udt-rep-090); mandate T10(b)
Kind: P
Fidelity: exact
Hyps: (a) full-support prior; `ε = 0` -/
theorem edt_rule_oneBoxes_on_full_of_eps_zero {μ : FinDist TPolicy} (hμ : ∀ π, 0 < μ.w π) :
    edtScore μ 0 .full .two < edtScore μ 0 .full .one := by
  rw [separation_vanishes_of_null_event (mass_full_two_eq_zero_of_eps_zero μ),
    edtScore_eq_of_pos (mass_full_one_pos hμ le_rfl one_pos)]
  norm_num [u]

/-! ### T10(c): the C&T rule is a third object -/

/-- **The C&T rule** at observation `o`: `E[U | Π o = a]` under the prior — condition on the
*policy's* action at `o`, no conditioning on the observation ([[notation]] §3.2; C&T's rule at
[[communication-trust-translated]] lines 441–442), junk `-1`.
Source: [[notation]] §3.2; [[communication-trust-translated]] lines 441–442 (udt-rep-090, 2-004)
Kind: D
Fidelity: exact (the prior over the agent's own policy made explicit)
Hyps: n/a -/
def ctScore (μ : FinDist TPolicy) (ε : ℝ) (o : TObs) (a : BoxAct) : ℝ :=
  condExpJunk (jointW μ ε) payoffΩ (event fun ω => ω.1 o = a) (-1)

/-- A sum over an event of the joint carrier that constrains only the policy, as a sum over
policies of coin sums.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_event_fst (P : TPolicy → Prop) [DecidablePred P] (g : TPolicy × Bool → ℝ) :
    ∑ ω ∈ event (fun ω : TPolicy × Bool => P ω.1), g ω = ∑ π ∈ event P, ∑ c, g (π, c) := by
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun π _ => ?_
  by_cases hP : P π <;> simp [hP]

/-- The same with the coin also constrained.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_event_fst_snd (P : TPolicy → Prop) [DecidablePred P] (b : Bool)
    (g : TPolicy × Bool → ℝ) :
    ∑ ω ∈ event (fun ω : TPolicy × Bool => P ω.1 ∧ ω.2 = b), g ω = ∑ π ∈ event P, g (π, b) := by
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun π _ => ?_
  by_cases hP : P π
  · simp only [hP, true_and, if_true]
    rw [Fintype.sum_bool]
    cases b <;> simp
  · simp [hP]

/-- Supporting lemma `sum_jointW_coin` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_jointW_coin (μ : FinDist TPolicy) (ε : ℝ) (π : TPolicy) :
    ∑ c, jointW μ ε (π, c) = μ.w π := by
  simp only [jointW, ← Finset.mul_sum, coinW_sum, mul_one]

/-- Supporting lemma `sum_jointW_payoff_coin` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_jointW_payoff_coin (μ : FinDist TPolicy) (ε : ℝ) (π : TPolicy) :
    ∑ c, jointW μ ε (π, c) * payoffΩ (π, c) = μ.w π * V ε π := by
  simp only [jointW, payoffΩ, V, Finset.mul_sum, mul_assoc]

/-- **The C&T rule reduces to the prior over policies**: `E[U | Π o = a]` is the `μ`-average of the
policy values `V ε π` over `{π : π o = a}`.
Source: [[notation]] §3.2 (udt-rep-090's bridge)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem ctScore_eq (μ : FinDist TPolicy) (ε : ℝ) (o : TObs) (a : BoxAct) :
    ctScore μ ε o a = condExpJunk μ.w (V ε) (event fun π => π o = a) (-1) := by
  simp only [ctScore, condExpJunk, mass]
  rw [sum_event_fst (fun π => π o = a), sum_event_fst (fun π => π o = a)]
  simp only [sum_jointW_coin, sum_jointW_payoff_coin]

/-- Supporting lemma `V_ge_of_full_one` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem V_ge_of_full_one {ε : ℝ} (h0 : 0 ≤ ε) (π : TPolicy) (h : π TObs.full = .one) :
    (1 - ε) * 1000000 ≤ V ε π := by
  rw [policy_eq_mk π, h]
  rcases π TObs.empty with _ | _
  · rw [V_oneOne]
  · rw [V_oneTwo]
    linarith

/-- Supporting lemma `V_le_of_full_two` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem V_le_of_full_two {ε : ℝ} (h1 : ε ≤ 1) (π : TPolicy) (h : π TObs.full = .two) :
    V ε π ≤ (1 - ε) * 1000 + ε * 1001000 := by
  rw [policy_eq_mk π, h]
  rcases π TObs.empty with _ | _
  · rw [V_twoOne]
    linarith
  · rw [V_twoTwo]

/-- **T10(c).** For every full-support prior and `ε < 999/2000`, the C&T rule strictly prefers
`one` at `full`: the minimum of `V ε` over the `one`-group, `(1−ε)·10⁶`, exceeds the maximum over
the `two`-group, `V ε (two,two)`, iff `999000(1−ε) > 1001000·ε` iff `ε < 999/2000`.
Source: [[notation]] §3.2; [[communication-trust-translated]] 441–442 (udt-rep-090's bridge, 2-004 instantiated)
Kind: P
Fidelity: exact
Hyps: (a) full-support prior, `0 ≤ ε ≤ 1`, `ε < 999/2000` (all explicit) -/
theorem ctRule_oneBoxes_on_full_of_lt {μ : FinDist TPolicy} {ε : ℝ} (hμ : ∀ π, 0 < μ.w π)
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hε : ε < 999 / 2000) :
    ctScore μ ε .full .two < ctScore μ ε .full .one := by
  rw [ctScore_eq, ctScore_eq]
  have hpos1 : 0 < mass μ.w (event fun π : TPolicy => π TObs.full = .one) :=
    mass_pos_of_mem μ.nonneg (x₀ := mk .one .one) (by simp) (hμ _)
  have hpos2 : 0 < mass μ.w (event fun π : TPolicy => π TObs.full = .two) :=
    mass_pos_of_mem μ.nonneg (x₀ := mk .two .two) (by simp) (hμ _)
  have hlow : (1 - ε) * 1000000 ≤ condExpJunk μ.w (V ε) (event fun π : TPolicy => π TObs.full = .one) (-1) :=
    le_condExpJunk_of_le μ.nonneg hpos1 fun π hπ => V_ge_of_full_one h0 π (by simpa using hπ)
  have hup : condExpJunk μ.w (V ε) (event fun π : TPolicy => π TObs.full = .two) (-1) ≤
      (1 - ε) * 1000 + ε * 1001000 :=
    condExpJunk_le_of_le μ.nonneg hpos2 fun π hπ => V_le_of_full_two h1 π (by simpa using hπ)
  linarith

/-- The prior `½δ_{(one,one)} + ½δ_{(two,two)}`.
Source: mandate T10(c)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def halfPrior : FinDist TPolicy := FinDist.halfHalf (mk .one .one) (mk .two .two)

/-- Supporting lemma `halfPrior_w` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem halfPrior_w (π : TPolicy) :
    halfPrior.w π =
      (if π = mk .one .one then 1 / 2 else 0) + (if π = mk .two .two then 1 - 1 / 2 else 0) :=
  rfl

/-- **T10(c), the disagreement at `empty`.** Under `halfPrior` and `ε = 1/10` the C&T rule strictly
prefers `one` at `empty` (`E[U | Π empty = one] = V(one,one) = 900000 > V(two,two) = 101000`), while
the UDT1.1 optimum `(one, two)` has `two` at `empty`. The rule the corpus writes as "UDT" agrees
with the policy optimum at `full` but can disagree at `empty`: the prior over one's own policy and
the `-1` convention are load-bearing in both directions.
Source: [[notation]] §3.2 (udt-rep-090's bridge finding); mandate T10(c)
Kind: P
Fidelity: exact
Hyps: (a) none (the prior and `ε` are the named witness) -/
theorem ctRule_disagrees_with_udt11_on_empty :
    ctScore halfPrior (1 / 10) .empty .two < ctScore halfPrior (1 / 10) .empty .one ∧
      IsOptimal (V (1 / 10)) (mk .one .two) ∧ mk .one .two TObs.empty = .two := by
  refine ⟨?_, (isOptimal_oneTwo_iff (by norm_num) (by norm_num)).mpr (by norm_num), rfl⟩
  rw [ctScore_eq, ctScore_eq]
  have e1 : condExpJunk halfPrior.w (V (1 / 10)) (event fun π : TPolicy => π TObs.empty = .one) (-1)
      = 900000 := by
    have hpos : 0 < mass halfPrior.w (event fun π : TPolicy => π TObs.empty = .one) := by
      rw [mass, Finset.sum_filter, tpolicy_sum]
      simp only [halfPrior_w, mk_empty, mk_inj, one_eq_two_iff, two_eq_one_iff]
      norm_num
    rw [condExpJunk_of_pos hpos, mass, Finset.sum_filter, Finset.sum_filter, tpolicy_sum, tpolicy_sum]
    simp only [halfPrior_w, mk_empty, mk_inj, one_eq_two_iff, two_eq_one_iff, V_oneOne, V_oneTwo,
      V_twoOne, V_twoTwo]
    norm_num
  have e2 : condExpJunk halfPrior.w (V (1 / 10)) (event fun π : TPolicy => π TObs.empty = .two) (-1)
      = 101000 := by
    have hpos : 0 < mass halfPrior.w (event fun π : TPolicy => π TObs.empty = .two) := by
      rw [mass, Finset.sum_filter, tpolicy_sum]
      simp only [halfPrior_w, mk_empty, mk_inj, one_eq_two_iff, two_eq_one_iff]
      norm_num
    rw [condExpJunk_of_pos hpos, mass, Finset.sum_filter, Finset.sum_filter, tpolicy_sum, tpolicy_sum]
    simp only [halfPrior_w, mk_empty, mk_inj, one_eq_two_iff, two_eq_one_iff, V_oneOne, V_oneTwo,
      V_twoOne, V_twoTwo]
    norm_num
  rw [e1, e2]
  norm_num

/-! ### T10(d): "UDT agents won't see the empty box" -/

/-- Supporting lemma `event_inter`: the intersection of two events is the event of the conjunction.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem event_inter {X : Type} [Fintype X] [DecidableEq X] (P Q : X → Prop) [DecidablePred P] [DecidablePred Q] :
    event P ∩ event Q = event fun x => P x ∧ Q x := by
  ext x
  simp

/-- Supporting lemma `event_empty_full_one` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem event_empty_full_one :
    (event fun ω : TPolicy × Bool => obsΩ ω = .empty ∧ ω.1 TObs.full = .one) =
      event fun ω : TPolicy × Bool => ω.1 TObs.full = .one ∧ ω.2 = false := by
  ext ⟨π, c⟩
  simp only [mem_event, obsΩ, obs, prediction]
  cases c <;> by_cases h : π TObs.full = .one <;> simp [h, flip]

/-- Supporting lemma `event_empty_full_two` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem event_empty_full_two :
    (event fun ω : TPolicy × Bool => obsΩ ω = .empty ∧ ω.1 TObs.full = .two) =
      event fun ω : TPolicy × Bool => ω.1 TObs.full = .two ∧ ω.2 = true := by
  ext ⟨π, c⟩
  simp only [mem_event, obsΩ, obs, prediction]
  cases c <;> rcases h : π TObs.full with _ | _ <;> simp [h, flip]

/-- **T10(d) (udt-rep-2-006(a)).** `P(O = empty | Π full = one) = ε` for a prior giving positive
mass to full-box one-boxers: "UDT agents won't see the empty box" is this with `ε → 0`.
Source: [[daniel-h-challenge]] "Decision Theory is for Making Bad Outcomes Inconsistent" (udt-rep-2-006(a))
Kind: L
Fidelity: exact
Hyps: (a) positive mass of the conditioning set (explicit) -/
theorem condProb_empty_given_full_one {μ : FinDist TPolicy} (ε : ℝ)
    (hμ : 0 < mass μ.w (event fun π : TPolicy => π TObs.full = .one)) :
    condProbJunk (jointW μ ε) (event fun ω => obsΩ ω = .empty)
      (event fun ω : TPolicy × Bool => ω.1 TObs.full = .one) (-1) = ε := by
  have hF : mass (jointW μ ε) (event fun ω : TPolicy × Bool => ω.1 TObs.full = .one) =
      mass μ.w (event fun π : TPolicy => π TObs.full = .one) := by
    simp only [mass]
    rw [sum_event_fst (fun π => π TObs.full = .one)]
    simp only [sum_jointW_coin]
  have hEF : mass (jointW μ ε) (event (fun ω => obsΩ ω = .empty) ∩
      event fun ω : TPolicy × Bool => ω.1 TObs.full = .one) =
      ε * mass μ.w (event fun π : TPolicy => π TObs.full = .one) := by
    rw [event_inter, event_empty_full_one]
    simp only [mass]
    rw [sum_event_fst_snd (fun π => π TObs.full = .one) false, Finset.mul_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    simp [jointW, coinW, mul_comm]
  simp only [condProbJunk, hF, hEF, hμ.ne', if_false]
  field_simp

/-- **T10(d) (udt-rep-2-006(a)).** `P(O = empty | Π full = two) = 1 − ε`.
Source: [[daniel-h-challenge]] (udt-rep-2-006(a))
Kind: L
Fidelity: exact
Hyps: (a) positive mass of the conditioning set (explicit) -/
theorem condProb_empty_given_full_two {μ : FinDist TPolicy} (ε : ℝ)
    (hμ : 0 < mass μ.w (event fun π : TPolicy => π TObs.full = .two)) :
    condProbJunk (jointW μ ε) (event fun ω => obsΩ ω = .empty)
      (event fun ω : TPolicy × Bool => ω.1 TObs.full = .two) (-1) = 1 - ε := by
  have hF : mass (jointW μ ε) (event fun ω : TPolicy × Bool => ω.1 TObs.full = .two) =
      mass μ.w (event fun π : TPolicy => π TObs.full = .two) := by
    simp only [mass]
    rw [sum_event_fst (fun π => π TObs.full = .two)]
    simp only [sum_jointW_coin]
  have hEF : mass (jointW μ ε) (event (fun ω => obsΩ ω = .empty) ∩
      event fun ω : TPolicy × Bool => ω.1 TObs.full = .two) =
      (1 - ε) * mass μ.w (event fun π : TPolicy => π TObs.full = .two) := by
    rw [event_inter, event_empty_full_two]
    simp only [mass]
    rw [sum_event_fst_snd (fun π => π TObs.full = .two) true, Finset.mul_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    simp [jointW, coinW, mul_comm]
  simp only [condProbJunk, hF, hEF, hμ.ne', if_false]
  field_simp

end Transparent

end

end Cleanroom.Udt.UdtPolicyCalc
