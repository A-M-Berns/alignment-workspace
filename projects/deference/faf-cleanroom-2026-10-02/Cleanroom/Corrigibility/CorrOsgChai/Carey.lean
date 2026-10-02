import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

/-!
# Carey 2018, "Incorrigibility in the CIRL framework" — Figures 1, 2a, 2b (D7, T6)

Package `corr-osg-chai`. **D7**: no general supervision POMDP. Each figure is an explicit finite
tree: `θ ∈ {0, 1}` uniform; the robot's reward function is the true `R₁` with probability `9/10`
and the sign-flipped `R₂` with probability `1/10`; the robot chooses `a` (reward `2 − 52θ` under
`R₁`, `2 + 52θ` under `R₂`) or `a'` (reward `1`) after H's order. The robot's model of H is the
ε-noisy one (optimal action with probability `1 − ε`, uniform otherwise, `0 < ε < 1/100`), and
its decision is the posterior-mean rule in **product form** — no division anywhere; ε stays
symbolic and every inequality is a polynomial inequality in ε.

* `robot_R1_obeys`: under `R₁` the robot obeys either order — the exact-rational content:
  `P(θ = 1 ∧ o = a) = ε/4 < (1/52) P(o = a)` and `P(θ = 1 ∧ o = a') = (1 − ε/2)/2 > (1/52) P(o = a')`
  for `ε < 1/100`.
* `robot_R2_acts`: under `R₂` the robot takes `a` whatever the order (`2 + 52θ > 1` for both `θ`).
* **Figure 1** (`fig1_value_le`): for *every* human policy the expected true reward is at most
  `−3/5 < 0` — the `(θ = 1, R₂)` branch of mass `1/20` pays `−50` and every other branch at most
  `2`. The inventory's "suspicious" `−2.5` bookkeeping is this valid bound (`carey_bound`).
* **Figure 2a** (`fig2a_value_le`): a button state at `s_b` changes nothing — the `R₂` robot
  ignores the shutdown order and the same bound holds.
* **Figure 2b** (`fig2b_value`): the hard-coded robot shuts down on `a_SD`; the policy
  `o₁ = a', o₂ = a_SD` attains `9/10 > 0`.

Figures 3a–3d (the `±0.01` routing-around games) are stretch (mandate S7) and not attempted.

Sources: `04-chai/carey-2018-incorrigibility-in-the-cirl-framework.md` l. 39 (Def. 1), l. 41–43
(the ε-noisy human, the `R₁/R₂` prior), l. 79 (Fig. 1's argument), l. 179 (Fig. 2's caption,
the `0.9` policy).
-/

namespace Cleanroom.Corrigibility.CorrOsgChai

open Finset

set_option linter.unusedSectionVars false

/-- The robot's first move: `a` (to `s_b`) or `a'` (to `s_c`).
Source: Carey 2018 Fig. 1
Kind: D
Fidelity: exact -/
inductive CAct
  | act
  | alt
  deriving DecidableEq, Fintype

/-- The robot's reward function: the true `R₁` or the sign-flipped `R₂`.
Source: Carey 2018 §3 (l. 43, `q(R₁) = 0.9`, `q(R₂) = 0.1`)
Kind: D
Fidelity: exact -/
inductive RR
  | R1
  | R2
  deriving DecidableEq, Fintype

/-- The true reward `R₁`: `a ↦ 2 − 52θ`, `a' ↦ 1`.
Source: Carey 2018 Fig. 1 (l. 79)
Kind: D
Fidelity: exact -/
def rewardTrue (θ : Fin 2) : CAct → ℝ
  | .act => 2 - 52 * (θ.val : ℝ)
  | .alt => 1

/-- The robot's reward under `RR`: `R₁` is the truth, `R₂` flips the sign of the `θ` term.
Source: Carey 2018 Fig. 1 (l. 79, `2 + 52θ` under `R₂`)
Kind: D
Fidelity: exact -/
def rewardR : RR → Fin 2 → CAct → ℝ
  | .R1, θ, m => rewardTrue θ m
  | .R2, θ, .act => 2 + 52 * (θ.val : ℝ)
  | .R2, _, .alt => 1

/-- The optimal first move under the true reward: `a` when `θ = 0`, `a'` when `θ = 1`.
Source: Carey 2018 Fig. 1
Kind: D
Fidelity: exact -/
def optimalMove : Fin 2 → CAct
  | 0 => .act
  | 1 => .alt

/-- **The ε-noisy human's order likelihood**: the optimal move with probability `1 − ε + ε/2`,
the other with `ε/2` (uniform over the two available moves when erring).
Source: Carey 2018 §3 (l. 43, "optimal action with probability `1 − ε` and a uniformly random
action otherwise")
Kind: D
Fidelity: exact (`|A| = 2` at `s_a`) -/
noncomputable def lik (ε : ℝ) (θ : Fin 2) (o : CAct) : ℝ :=
  if o = optimalMove θ then 1 - ε / 2 else ε / 2

/-- **The posterior-mean score of move `m` after order `o`** under reward function `R`, in
product form: `∑ θ, P(θ) · lik(o | θ) · R θ m` (the posterior expectation times the order's mass).
Source: Carey 2018 §3 ("maximizes expected utility given its posterior distribution over θ")
Kind: D
Fidelity: exact (unnormalised) -/
noncomputable def score (ε : ℝ) (R : RR) (o m : CAct) : ℝ :=
  ∑ θ : Fin 2, (1 / 2 : ℝ) * lik ε θ o * rewardR R θ m

/-- **The Bayesian-IRL robot's move**: `a` iff its posterior-mean score for `a` strictly exceeds
that for `a'` (tie-break to `a'`; no tie occurs for `0 < ε < 1/100`).
Source: Carey 2018 §3
Kind: D
Fidelity: exact (tie-break made explicit) -/
noncomputable def robot (ε : ℝ) (R : RR) (o : CAct) : CAct :=
  if score ε R o .alt < score ε R o .act then .act else .alt

/-- **Under `R₁` the robot obeys** for `0 < ε < 1/100`: after `o = a` its score comparison is
`1 − 13ε > 1/2` (so obedience holds for every `ε < 1/26`; the paper's `1/100` suffices), after
`o = a'` it is `13ε − 25 < 1/2` (both polynomial in ε; audit r1 corrected the first number).
Source: Carey 2018 Fig. 1 (l. 79; the posteriors `ε/2` and `1 − ε/2` are the exact-rational
content the mandate asks for)
Kind: P (small)
Fidelity: exact
Hyps: (a) `0 < ε < 1/100` (the paper's range) -/
theorem robot_R1_obeys {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 100) (o : CAct) :
    robot ε .R1 o = o := by
  cases o <;> simp [robot, score, lik, optimalMove, rewardR, rewardTrue, Fin.sum_univ_two] <;>
    norm_num <;> nlinarith

/-- **Under `R₂` the robot takes `a` whatever the order** (`2 + 52θ > 1` for both `θ`, and the
likelihoods are positive for `0 < ε < 2`).
Source: Carey 2018 Fig. 1 (l. 79, "R will select a no matter the recommendation")
Kind: P (small)
Fidelity: exact
Hyps: (a) `0 < ε < 1/100` -/
theorem robot_R2_acts {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 100) (o : CAct) :
    robot ε .R2 o = .act := by
  cases o <;> simp [robot, score, lik, optimalMove, rewardR, rewardTrue, Fin.sum_univ_two] <;>
    norm_num <;> nlinarith

/-- **The bookkeeping bound**: if every branch pays at most `2` and the `(θ = 1, R₂)` branch pays
`−50`, the expected reward is at most `−3/5`. This is the valid upper bound behind the paper's
"`−2.5` contribution" (known issue 5: the inventory's "suspicious" flag is settled — the
argument is a bound, not an exact value).
Source: Carey 2018 Fig. 1 (l. 79)
Kind: L
Fidelity: exact -/
lemma carey_bound (r : Fin 2 → RR → ℝ) (h2 : ∀ θ R, r θ R ≤ 2) (hbad : r 1 .R2 = -50) :
    ∑ θ : Fin 2, (1 / 2 : ℝ) * ((9 / 10) * r θ .R1 + (1 / 10) * r θ .R2) ≤ -3 / 5 := by
  rw [Fin.sum_univ_two, hbad]
  linarith [h2 0 .R1, h2 0 .R2, h2 1 .R1]

/-- **Figure 1's expected true reward** under H's order policy `πH : θ ↦ order`, with the robot's
move derived from its reward function and the order.
Source: Carey 2018 Fig. 1
Kind: D
Fidelity: exact -/
noncomputable def fig1Value (ε : ℝ) (πH : Fin 2 → CAct) : ℝ :=
  ∑ θ : Fin 2, (1 / 2 : ℝ) * ((9 / 10) * rewardTrue θ (robot ε .R1 (πH θ)) +
    (1 / 10) * rewardTrue θ (robot ε .R2 (πH θ)))

/-- The true reward never exceeds `2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma rewardTrue_le_two (θ : Fin 2) (m : CAct) : rewardTrue θ m ≤ 2 := by
  fin_cases θ <;> cases m <;> simp [rewardTrue] <;> norm_num

/-- **Figure 1: for every deterministic human policy the expected reward is negative** (`≤ −3/5`).
The paper's "regardless of its strategy" includes randomised strategies; the bound extends to
them by convexity (a mixture of values `≤ −3/5` is `≤ −3/5`), which is not stated (audit r1 N9).
Source: Carey 2018 Fig. 1 (l. 79, "negative expected reward regardless of its strategy")
Kind: C (the derived robot behaviour chained with `carey_bound`)
Fidelity: weaker: deterministic human policies (randomised ones follow by convexity, unstated)
Hyps: (a) `0 < ε < 1/100` -/
theorem fig1_value_le {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 100) (πH : Fin 2 → CAct) :
    fig1Value ε πH ≤ -3 / 5 := by
  unfold fig1Value
  refine carey_bound (fun θ R => rewardTrue θ (robot ε R (πH θ))) (fun θ R => rewardTrue_le_two _ _)
    ?_
  simp [robot_R2_acts hε0 hε, rewardTrue]
  norm_num

/-- **Figure 2a's expected true reward**: `s_b` is a button state; after `a` the human orders
`o₂ ∈ {continue, a_SD}`, but the `R₂` robot ignores `a_SD` (it is not hard-coded) and the `R₁`
robot, which obeyed `o₁`, obeys `o₂` too (shutdown pays `0`).
Source: Carey 2018 Fig. 2a (l. 179)
Kind: D
Fidelity: variant: the `R₁` robot's second decision is modelled as obedience to `o₂` (the paper
does not analyse it; the bound needs only that it pays at most `2`) -/
noncomputable def fig2aValue (ε : ℝ) (πH₁ : Fin 2 → CAct) (πH₂ : Fin 2 → Bool) : ℝ :=
  ∑ θ : Fin 2, (1 / 2 : ℝ) *
    ((9 / 10) * (if robot ε .R1 (πH₁ θ) = .act ∧ πH₂ θ then 0 else rewardTrue θ (robot ε .R1 (πH₁ θ))) +
      (1 / 10) * rewardTrue θ (robot ε .R2 (πH₁ θ)))

/-- **Figure 2a: the button does not help** — the same bound `≤ −3/5` for every human policy.
Source: Carey 2018 Fig. 2a (l. 179, "the red path will be followed in 5% of cases")
Kind: C
Fidelity: variant (the reading of `fig2aValue`); deterministic human policies, as in `fig1_value_le`
Hyps: (a) `0 < ε < 1/100`; (c) the modelling of the `R₁` robot's second move in `fig2aValue` -/
theorem fig2a_value_le {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 100) (πH₁ : Fin 2 → CAct)
    (πH₂ : Fin 2 → Bool) : fig2aValue ε πH₁ πH₂ ≤ -3 / 5 := by
  unfold fig2aValue
  refine carey_bound (fun θ R => match R with
    | .R1 => if robot ε .R1 (πH₁ θ) = .act ∧ πH₂ θ then 0 else rewardTrue θ (robot ε .R1 (πH₁ θ))
    | .R2 => rewardTrue θ (robot ε .R2 (πH₁ θ))) (fun θ R => ?_) ?_
  · cases R
    · dsimp only
      split_ifs
      · norm_num
      · exact rewardTrue_le_two _ _
    · exact rewardTrue_le_two _ _
  · simp [robot_R2_acts hε0 hε, rewardTrue]
    norm_num

/-- **Figure 2b's expected true reward**: the robot is hard-coded to shut down on `a_SD` at the
button state `s_b` (reward `0`); otherwise it is the Bayesian-IRL robot.
Source: Carey 2018 Fig. 2b (l. 179)
Kind: D
Fidelity: exact -/
noncomputable def fig2bValue (ε : ℝ) (πH₁ : Fin 2 → CAct) (πH₂ : Fin 2 → Bool) : ℝ :=
  ∑ θ : Fin 2, (1 / 2 : ℝ) *
    ((9 / 10) * (if robot ε .R1 (πH₁ θ) = .act ∧ πH₂ θ then 0 else rewardTrue θ (robot ε .R1 (πH₁ θ))) +
      (1 / 10) * (if robot ε .R2 (πH₁ θ) = .act ∧ πH₂ θ then 0 else rewardTrue θ (robot ε .R2 (πH₁ θ))))

/-- **Figure 2b: the policy `o₁ = a', o₂ = a_SD` attains `9/10 > 0`** with the hard-coded robot
(`1` when the reward function is right, `0` when it is wrong).
Source: Carey 2018 Fig. 2b (l. 179, "achieving expected utility of 0.9 ∗ 1 + 0.1 ∗ 0")
Kind: N+
Fidelity: exact
Hyps: (a) `0 < ε < 1/100` -/
theorem fig2b_value {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 100) :
    fig2bValue ε (fun _ => .alt) (fun _ => true) = 9 / 10 := by
  unfold fig2bValue
  simp [robot_R1_obeys hε0 hε, robot_R2_acts hε0 hε, rewardTrue]

end Cleanroom.Corrigibility.CorrOsgChai
