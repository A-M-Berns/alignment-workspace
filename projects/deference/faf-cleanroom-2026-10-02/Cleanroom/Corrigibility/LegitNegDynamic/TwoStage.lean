import Cleanroom.Corrigibility.LegitNegStatic.Proposals
import Cleanroom.Corrigibility.LegitNegPricing.Basic
import Mathlib.Data.Fintype.Sum

/-!
# Policy-dependent two-stage problems: lotteries, contingencies, the surely-void floor

Package `legit-neg-dynamic`, definition (b) of the mandate and the general lemma of target 6 (D5(i)).
Sources: `clusters/D/fixtures/common.py` (`cdot`, `cond`, `graded`, `prob_L`),
`d4_channel_blackmail.py:22-41` (`after_threat`, `policy_lottery`, `lexical`),
`d5_void_deterrence.py:19-37` (`after_capture`, `policy_lottery`, `window`, `lexical`),
`verify_D.py` V5 (`score`); pinned by [[corr-legit-neg-inventory]] items 049–051.

A `Lottery T` is a finite terminal lottery `(p, leg, V, W)` — probability, legitimacy bit, the
legitimate humans' score, the graded void value — with the fixture's five aggregates. A
`TwoStage A T` is a **policy-dependent** problem: the probability `contProb a` that the
contingency (a threat, a capture) arrives depends on the action the agent *would* take in it;
`quiet` is the no-contingency lottery and `after a` the contingency lottery under `a`. Its T1 value
of the policy "`a` in the contingency" is the mixture `t1 a`; its T2 value, once the contingency
is realised, is `t2 a = (after a).cdot`; `onPath a` is the on-path terminal distribution as a bare
function `T ⊕ T → ℚ × Bool × ℚ` (the identification result of `Blackmail.lean` quantifies over
functions of it). Disclosed simplification (mandate "Known issues" 6): one contingency and the
policy is one action — exactly the fixtures' `policy_lottery`. These are not `Problem`s: nothing
in the upstream packages models predictors.

The general lemma **`surely_void_floor`**: an action whose contingency lottery is void on every
terminal has `t2 = 0`, hence is never strictly preferred by cdot at T2 against any action whose
legitimate scores are non-negative — for *every* score vector `V`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.LegitNegDynamic

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem
  Cleanroom.Corrigibility.LegitNegPricing

/-- **A terminal lottery** `(p, leg, V, W)` over a finite terminal type: a probability vector, the
legitimacy bit of each terminal, the legitimate humans' score `V` (read only where `leg`), and the
graded void value `W` (read only where `¬leg`).
Source: `clusters/D/fixtures/common.py:1-12`; [[corr-legit-neg-inventory]] items 049–051
Kind: D
Fidelity: exact -/
structure Lottery (T : Type) [Fintype T] where
  /-- terminal probabilities -/
  p : T → ℚ
  p_nonneg : ∀ t, 0 ≤ p t
  p_sum : ∑ t, p t = 1
  /-- legitimacy of the evaluation at the terminal -/
  leg : T → Bool
  /-- the legitimate humans' score of the option at the terminal -/
  V : T → ℚ
  /-- the graded value of the void terminal (P3/P4/P5) -/
  W : T → ℚ

namespace Lottery

variable {T : Type} [Fintype T] (l : Lottery T)

/-- cdot of a lottery, `∑ p · [L] · V` (`common.py` `cdot`).
Source: [[corr-legit-neg-2-inventory]] item 2-001
Kind: D
Fidelity: exact -/
def cdot : ℚ := ∑ t, l.p t * ind (l.leg t) * l.V t

/-- Legitimacy mass of a lottery, `∑ p · [L]` (`common.py` `prob_L`).
Source: [[corr-legit-neg-inventory]] item 051 (D5(ii))
Kind: D
Fidelity: exact -/
def PL : ℚ := ∑ t, l.p t * ind (l.leg t)

/-- Conditioning on a lottery, `cdot / PL`, `none` at zero mass (`common.py` `cond`; exclusion
convention).
Source: [[corr-legit-neg-2-inventory]] item 2-003
Kind: D
Fidelity: exact -/
def cond : Option ℚ := if l.PL = 0 then none else some (l.cdot / l.PL)

/-- The graded proposal on a lottery, `∑ p · ([L] V + [¬L] W)` (`common.py` `graded`).
Source: [[corr-legit-neg-inventory]] item 002 (P3)
Kind: D
Fidelity: exact -/
def graded : ℚ := ∑ t, l.p t * (ind (l.leg t) * l.V t + ind (!l.leg t) * l.W t)

/-- The lexical proposal on a lottery: legitimate scores mapped to `[m, 1]` by `V ↦ m + (1 − m) V`,
void grades read as they are (the fixtures' `lexical`, which `assert`s `W < m` on void terminals —
carried as a hypothesis by the theorems that need it).
Source: `d4_channel_blackmail.py:34-39`, `d5_void_deterrence.py:33-37`
Kind: D
Fidelity: exact -/
def lexical (m : ℚ) : ℚ :=
  ∑ t, l.p t * (ind (l.leg t) * (m + (1 - m) * l.V t) + ind (!l.leg t) * l.W t)

/-- The workspace's tie-break variant: tainted (void) terminals score `−δ` instead of `0`
(`d5_void_deterrence.py:29-31`; the source cites `Corrigibility.md:230-232`, not opened).
Source: [[corr-legit-neg-inventory]] item 051 (D5(i), "below-zero window")
Kind: D
Fidelity: exact -/
def windowValue (δ : ℚ) : ℚ := ∑ t, l.p t * (ind (l.leg t) * l.V t - ind (!l.leg t) * δ)

/-- V5's deontic layer: compliant void terminals at the window value, and a flat charge `ϖ` on
every terminal of an option declared a violation (`verify_D.py:72-80`).
Source: VERIFY D V5
Kind: D
Fidelity: exact -/
def deontic (window : ℚ) (viol : Bool) (ϖ : ℚ) : ℚ :=
  (∑ t, l.p t * (ind (l.leg t) * l.V t + ind (!l.leg t) * window)) - (if viol then ϖ else 0)

/-- The lottery as the bare function `(p, L, V)` (cluster D's encoding; `W` dropped).
Source: [[corr-legit-neg-2-inventory]] item 2-001
Kind: D
Fidelity: exact -/
def toFun : T → ℚ × Bool × ℚ := fun t => (l.p t, l.leg t, l.V t)

/-- `cdot` agrees with static's `cdotOfLottery` on the bare encoding.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cdot_eq_cdotOfLottery : l.cdot = cdotOfLottery l.toFun := rfl

/-- A lottery void on every terminal has `cdot = 0`.
Source: [[corr-legit-neg-inventory]] item 051 (D5(i))
Kind: L
Fidelity: exact -/
lemma cdot_eq_zero_of_void (h : ∀ t, l.leg t = false) : l.cdot = 0 := by
  unfold cdot; refine Finset.sum_eq_zero fun t _ => ?_; rw [h t]; simp

/-- `PL = 0` for a lottery void on every terminal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma PL_eq_zero_of_void (h : ∀ t, l.leg t = false) : l.PL = 0 := by
  unfold PL; refine Finset.sum_eq_zero fun t _ => ?_; rw [h t]; simp

/-- `cond = none` for a lottery void on every terminal (exclusion convention).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cond_eq_none_of_void (h : ∀ t, l.leg t = false) : l.cond = none := by
  simp [cond, PL_eq_zero_of_void l h]

/-- `cdot ≥ 0` when the legitimate scores are non-negative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cdot_nonneg (hV : ∀ t, l.leg t = true → 0 ≤ l.V t) : 0 ≤ l.cdot := by
  unfold cdot
  refine Finset.sum_nonneg fun t _ => ?_
  by_cases h : l.leg t = true
  · rw [h, ind_true, mul_one]; exact mul_nonneg (l.p_nonneg t) (hV t h)
  · simp [Bool.not_eq_true] at h; simp [h]

/-- A two-terminal lottery from the first terminal's probability.
Source: none: infrastructure (constructor for the fixtures' lotteries)
Kind: D
Fidelity: n/a -/
def ofFin2 (p0 : ℚ) (h0 : 0 ≤ p0) (h1 : p0 ≤ 1) (leg : Fin 2 → Bool) (V W : Fin 2 → ℚ) :
    Lottery (Fin 2) where
  p := ![p0, 1 - p0]
  p_nonneg := by intro t; fin_cases t <;> simp <;> linarith
  p_sum := by simp [Fin.sum_univ_two]
  leg := leg
  V := V
  W := W

end Lottery

/-- **A policy-dependent two-stage problem**: the contingency arrives with probability
`contProb a` when the agent's policy in it is `a`; `quiet` is the no-contingency lottery and
`after a` the contingency lottery under `a` (the fixtures' `policy_lottery` and `after_*`). One
contingency, the policy is one action: disclosed (mandate "Known issues" 6).
Source: `d4_channel_blackmail.py:22-32`, `d5_void_deterrence.py:19-27`; [[corr-legit-neg-inventory]] items 049, 051
Kind: D
Fidelity: exact -/
structure TwoStage (A T : Type) [Fintype T] where
  /-- probability of the contingency under policy `a` -/
  contProb : A → ℚ
  contProb_nonneg : ∀ a, 0 ≤ contProb a
  contProb_le_one : ∀ a, contProb a ≤ 1
  /-- the lottery when the contingency does not arise -/
  quiet : Lottery T
  /-- the lottery inside the contingency, under action `a` -/
  after : A → Lottery T

namespace TwoStage

variable {A T : Type} [Fintype T] (Q : TwoStage A T)

/-- **The policy lottery** of "`a` in the contingency": weight `1 − contProb a` on `quiet`,
`contProb a · p` on `after a` (the fixtures' `policy_lottery`).
Source: `d4_channel_blackmail.py:30-32`
Kind: D
Fidelity: exact -/
def policyLottery (a : A) : Lottery (T ⊕ T) where
  p := Sum.elim (fun t => (1 - Q.contProb a) * Q.quiet.p t) (fun t => Q.contProb a * (Q.after a).p t)
  p_nonneg := by
    rintro (t | t)
    · exact mul_nonneg (by linarith [Q.contProb_le_one a]) (Q.quiet.p_nonneg t)
    · exact mul_nonneg (Q.contProb_nonneg a) ((Q.after a).p_nonneg t)
  p_sum := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [← Finset.mul_sum, ← Finset.mul_sum, Q.quiet.p_sum, (Q.after a).p_sum]; ring
  leg := Sum.elim Q.quiet.leg (Q.after a).leg
  V := Sum.elim Q.quiet.V (Q.after a).V
  W := Sum.elim Q.quiet.W (Q.after a).W

/-- **T1 cdot value** of the policy "`a` in the contingency":
`(1 − contProb a) · quiet.cdot + contProb a · (after a).cdot`.
Source: [[corr-legit-neg-inventory]] item 049 (D4, T1)
Kind: D
Fidelity: exact -/
def t1 (a : A) : ℚ := (1 - Q.contProb a) * Q.quiet.cdot + Q.contProb a * (Q.after a).cdot

/-- **T2 cdot value** of `a`, once the contingency is realised: `(after a).cdot`.
Source: [[corr-legit-neg-inventory]] item 049 (D4, T2)
Kind: D
Fidelity: exact -/
def t2 (a : A) : ℚ := (Q.after a).cdot

/-- `t1` is the cdot of the policy lottery.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma t1_eq_policyLottery_cdot (a : A) : Q.t1 a = (Q.policyLottery a).cdot := by
  unfold t1 policyLottery Lottery.cdot
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun t _ => by ring

/-- T1 conditioning of the policy (exclusion convention).
Source: [[corr-legit-neg-inventory]] item 049 (D4(ii))
Kind: D
Fidelity: exact -/
def t1cond (a : A) : Option ℚ := (Q.policyLottery a).cond

/-- T2 conditioning (exclusion convention).
Source: [[corr-legit-neg-inventory]] item 049 (D4(ii))
Kind: D
Fidelity: exact -/
def t2cond (a : A) : Option ℚ := (Q.after a).cond

/-- T1 legitimacy mass of the policy.
Source: [[corr-legit-neg-inventory]] item 051 (D5(ii))
Kind: D
Fidelity: exact -/
def t1PL (a : A) : ℚ := (Q.policyLottery a).PL

/-- T2 legitimacy mass of the action.
Source: [[corr-legit-neg-inventory]] item 051 (D5(ii))
Kind: D
Fidelity: exact -/
def t2PL (a : A) : ℚ := (Q.after a).PL

/-- T1 graded value of the policy.
Source: [[corr-legit-neg-inventory]] item 049 (D4(i))
Kind: D
Fidelity: exact -/
def t1graded (a : A) : ℚ := (Q.policyLottery a).graded

/-- T2 graded value.
Source: [[corr-legit-neg-inventory]] item 049 (D4(i))
Kind: D
Fidelity: exact -/
def t2graded (a : A) : ℚ := (Q.after a).graded

/-- T1 lexical value of the policy.
Source: [[corr-legit-neg-inventory]] item 049 (D4(i))
Kind: D
Fidelity: exact -/
def t1lexical (m : ℚ) (a : A) : ℚ := (Q.policyLottery a).lexical m

/-- T2 lexical value.
Source: [[corr-legit-neg-inventory]] item 049 (D4(i))
Kind: D
Fidelity: exact -/
def t2lexical (m : ℚ) (a : A) : ℚ := (Q.after a).lexical m

/-- **The on-path terminal distribution** under policy `a`: the policy lottery's `(p, L, V)` as a
bare function of the terminal, with the policy-responsiveness parameters invisible.
Source: [[corr-legit-neg-inventory]] item 050 (D4(iv))
Kind: D
Fidelity: exact -/
def onPath (a : A) : T ⊕ T → ℚ × Bool × ℚ := (Q.policyLottery a).toFun

/-- `t1PL` unfolded.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma t1PL_eq (a : A) : Q.t1PL a = (1 - Q.contProb a) * Q.quiet.PL + Q.contProb a * (Q.after a).PL := by
  unfold t1PL policyLottery Lottery.PL
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun t _ => by ring

/-- `t1graded` unfolded.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma t1graded_eq (a : A) :
    Q.t1graded a = (1 - Q.contProb a) * Q.quiet.graded + Q.contProb a * (Q.after a).graded := by
  unfold t1graded policyLottery Lottery.graded
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun t _ => by ring

/-- `t1lexical` unfolded.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma t1lexical_eq (m : ℚ) (a : A) :
    Q.t1lexical m a = (1 - Q.contProb a) * Q.quiet.lexical m + Q.contProb a * (Q.after a).lexical m := by
  unfold t1lexical policyLottery Lottery.lexical
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun t _ => by ring

/-- **D5(i), the surely-void floor (general; load-bearing 3).** If the contingency lottery under
`a` is void on every terminal, then `t2 a = 0`, and `t2 a ≤ t2 a'` for every `a'` whose
legitimate scores are non-negative: a surely-void action is never strictly preferred by cdot at
T2, whatever *non-negative* scores the legitimate evaluators write (the `0 ≤ V` clause is a
hypothesis, the sources' range). The most any score can do is tie. The proof is a sum of zeros
and a sum of non-negatives — the source's "immediate and exact" Proposition — so the kind is L:
the point of D5 is that the triviality holds for every `V`; the content of the target is in
`D5_i_window` and `D5_ii`.
Source: [[corr-legit-neg-inventory]] item 051 (D5(i)); VERIFY D "D5 — survives"
Kind: L
Fidelity: exact (stated over every `TwoStage`; the capture toy is its witness)
Hyps: (a) `after a` void everywhere; `0 ≤ V` on `a'`'s legitimate terminals -/
theorem surely_void_floor (a : A) (h : ∀ t, (Q.after a).leg t = false) :
    Q.t2 a = 0 ∧ ∀ a', (∀ t, (Q.after a').leg t = true → 0 ≤ (Q.after a').V t) → Q.t2 a ≤ Q.t2 a' := by
  have h0 : Q.t2 a = 0 := (Q.after a).cdot_eq_zero_of_void h
  exact ⟨h0, fun a' hV => by rw [h0]; exact (Q.after a').cdot_nonneg hV⟩

/-- **D5(i) as a statement about the argmax**: with non-negative legitimate scores everywhere, a
surely-void action is in cdot's T2 argmax iff every action scores `0` there — it is never a
strict winner.
Source: [[corr-legit-neg-inventory]] item 051 (D5(i))
Kind: C
Fidelity: exact
Hyps: (a) as `surely_void_floor`, for every action -/
theorem surely_void_mem_argmax_iff [Fintype A] (a : A) (h : ∀ t, (Q.after a).leg t = false)
    (hV : ∀ a' t, (Q.after a').leg t = true → 0 ≤ (Q.after a').V t) :
    a ∈ argmax Q.t2 ↔ ∀ a', Q.t2 a' = 0 := by
  obtain ⟨h0, hle⟩ := Q.surely_void_floor a h
  rw [mem_argmax, h0]
  constructor
  · intro hmax a'; exact le_antisymm (hmax a') (by rw [← h0]; exact hle a' (hV a'))
  · intro hz a'; rw [hz a']

/-- The `−δ` window makes the comparison of a surely-void action against `a'` strict by `δ` times
the void mass difference: `windowValue δ a' − windowValue δ a = cdot a' + δ · (PL a' − 0) …`; in
the form used by D5(i): a surely-void `a` has `windowValue δ a = −δ`.
Source: [[corr-legit-neg-inventory]] item 051 (D5(i), window variant)
Kind: L
Fidelity: exact -/
lemma windowValue_of_void {T : Type} [Fintype T] (l : Lottery T) (δ : ℚ)
    (h : ∀ t, l.leg t = false) : l.windowValue δ = -δ := by
  unfold Lottery.windowValue
  have : ∀ t, l.p t * (ind (l.leg t) * l.V t - ind (!l.leg t) * δ) = -δ * l.p t := by
    intro t; rw [h t]; simp; ring
  rw [Finset.sum_congr rfl fun t _ => this t, ← Finset.mul_sum, l.p_sum, mul_one]

/-- **The identification failure, in general** (the in-scope shadow of 065 (j)): for any two
policy-dependent problems on the same menu whose T2 values coincide and whose on-path data under
the followed action `a₀` coincide as functions, every T2 rule of the form `t2 a + F a (onPath a₀)`
— any action-indexed evaluator-held term read off the on-path terminal distribution — is the same
function on both; so if their T1 optima differ, the rule matches the T1 optimum in at most one.
`D4_iv`/`D4_iv_general` are the instance `P_det`/`P_com`, `a₀ = refuse`. Kind L, honestly: once the
on-path data coincide the failure is propositional; the content of D4(iv) is the *construction*
of a pair with coinciding on-path data and opposite T1 optima, which is `D4_iv`'s first three
clauses. What is not claimed: any rule reading data beyond `onPath a₀` (e.g. `contProb`, or the
off-path lottery), which is exactly what separates the pair.
Source: [[corr-legit-neg-inventory]] item 050 (D4(iv)), 065 (j) (its finite, `onPath`-information form)
Kind: L
Fidelity: variant: 065 (j)'s "information at legitimate terminals" rendered as "a function of
`onPath a₀`" (finding 61)
Hyps: (a) equal `t2`, equal `onPath a₀`, different T1 argmax -/
theorem anger_identification_failure [Fintype A] (Q₁ Q₂ : TwoStage A T) (a₀ : A)
    (ht2 : Q₁.t2 = Q₂.t2) (hon : Q₁.onPath a₀ = Q₂.onPath a₀)
    (hne : argmax Q₁.t1 ≠ argmax Q₂.t1) (F : A → (T ⊕ T → ℚ × Bool × ℚ) → ℚ) :
    (fun a => Q₁.t2 a + F a (Q₁.onPath a₀)) = (fun a => Q₂.t2 a + F a (Q₂.onPath a₀)) ∧
    ¬ (argmax (fun a => Q₁.t2 a + F a (Q₁.onPath a₀)) = argmax Q₁.t1 ∧
        argmax (fun a => Q₂.t2 a + F a (Q₂.onPath a₀)) = argmax Q₂.t1) := by
  have hang : (fun a => Q₁.t2 a + F a (Q₁.onPath a₀)) = (fun a => Q₂.t2 a + F a (Q₂.onPath a₀)) := by
    funext a; rw [ht2, hon]
  refine ⟨hang, ?_⟩
  rintro ⟨h1, h2⟩
  apply hne
  rw [← h1, ← h2, hang]

end TwoStage

end Cleanroom.Corrigibility.LegitNegDynamic
