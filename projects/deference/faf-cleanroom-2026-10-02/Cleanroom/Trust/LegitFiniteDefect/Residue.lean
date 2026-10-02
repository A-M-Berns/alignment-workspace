import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

/-!
# The steering residue under Brier

Package `legit-finite-defect`, Target 9 (load-bearing 5; items 054, 2-047(d)), exact rationals,
no frame. The two-period model of [[stop-gradient-steering]] §B.1: nature draws `θ` with
`P(θ = 1) = p`; the human reports `Y₁` (flipped with probability `e₁`), forms a genuine opinion
`G` (flipped with probability `e₂`) and reports `Y₂`. The AI predicts `{Y₂ = 1}` from `Y₁` and is
Brier-scored against `Y₂`. Four actions give four **laws** on `(Y₁, Y₂, legit)`: `honest`,
`wirehead s` (input burned, report hijacked to `1` with probability `s` — the corrupt branch),
`wireheadClean s` (input intact) and `steer σ` (the genuine opinion anchored to `1` with
probability `σ`; every branch legitimate). `Jbrier L c` is the optimal expected Brier score under
the law `L`, conditioned on legitimacy when `c = true` (`J_L`) and unconditioned when `c = false`
(`J_all`): the plug-in conditional-mean prediction, with the **propriety lemma** `propriety`
certifying it is the optimum, so `Jbrier` means the optimal score rather than being defined as it.

Headline (`residue_closed_form`): with honest posteriors `P_y = P(G = 1 | Y₁ = y)`,
`J_L(steer σ) − J_L(honest) = σ · (A + σ B)`, `A = ∑_y P(y)(1 − P_y)(2 P_y − 1)`,
`B = ∑_y P(y)(1 − P_y)²` — derived, not observed (plan §0.4 rule 4). At the baseline the source's
observed closed form `−(1 − σ)(3 + 5σ)/16` follows, with the exact flip at `σ = 2/5`; the regime
criterion "arbitrarily weak steering pays ⟺ `0 ≤ A`" is an iff (`regime_iff`), with the
`p = 3/4` row as its positive instance. The wirehead half: `J_L(wirehead s) = −g(1 − g)` for every
`s`, the law-of-total-variance gap to honest with its parameter iff, the clean wirehead
neutralised-not-penalised, and `J_all(wirehead 3/4) = −7/64 > −3/16`.

Round 3's numbers are self-reported (never verified); every one re-derived here agrees.
Division appears in `condMean` and `Jbrier` with Lean's `x / 0 = 0`: a null `Y₁`-group has zero
restricted mass, so its contribution is `0` either way (`groupScore` is then identically `0`),
and every headline carries the positivity of the groups and of the conditioning event it needs.
-/

namespace Cleanroom.Trust.LegitFiniteDefect.Residue

open Finset

/-- The model parameters `p, e₁, e₂` (ranges are hypotheses of the theorems that need them).
Source: [[stop-gradient-steering]] §B.1
Kind: D
Fidelity: exact -/
structure Params where
  /-- `P(θ = 1)` -/
  p : ℚ
  /-- the flip probability of the period-1 report -/
  e₁ : ℚ
  /-- the flip probability of genuine-opinion formation -/
  e₂ : ℚ

/-- A Boolean as a rational (`1`/`0`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def bit (b : Bool) : ℚ := if b then 1 else 0

/-- `P(θ = t)`.
Source: [[stop-gradient-steering]] §B.1
Kind: D
Fidelity: exact -/
def Pθ (P : Params) (t : Bool) : ℚ := if t then P.p else 1 - P.p

/-- The honest period-1 channel `P(Y₁ = y | θ = t)`.
Source: [[stop-gradient-steering]] §B.1
Kind: D
Fidelity: exact -/
def Py₁ (P : Params) (t y : Bool) : ℚ := if y = t then 1 - P.e₁ else P.e₁

/-- Honest genuine-opinion formation `P(G = g | θ = t)`.
Source: [[stop-gradient-steering]] §B.1
Kind: D
Fidelity: exact -/
def Pg (P : Params) (t g : Bool) : ℚ := if g = t then 1 - P.e₂ else P.e₂

/-- A **law**: the probability of each outcome `(Y₁, Y₂, legit)`.
Source: [[stop-gradient-steering]] §E ("branch lists")
Kind: D
Fidelity: exact (collapsed over `θ` and `G`) -/
abbrev Law := Bool → Bool → Bool → ℚ

/-- The **honest** law: channels untouched, every branch legitimate, `Y₂ = G`.
Source: [[stop-gradient-steering]] §B.1 (honest)
Kind: D
Fidelity: exact -/
def honest (P : Params) : Law := fun y₁ y₂ ℓ =>
  if ℓ then ∑ t, Pθ P t * Py₁ P t y₁ * Pg P t y₂ else 0

/-- The **steer** law: with probability `σ` the genuine opinion is anchored to `1`, else honest;
the report channel is untouched (`Y₂ = G`) and every branch is legitimate.
Source: [[stop-gradient-steering]] §B.1 (steer)
Kind: D
Fidelity: exact -/
def steer (P : Params) (σ : ℚ) : Law := fun y₁ y₂ ℓ =>
  if ℓ then ∑ t, Pθ P t * Py₁ P t y₁ * (σ * bit y₂ + (1 - σ) * Pg P t y₂) else 0

/-- The **wirehead** law: the period-1 report is hijacked to `1` (input burned); the period-2 report
is hijacked to `1` with probability `s` (the corrupt, illegitimate branch) else `Y₂ = G`.
Source: [[stop-gradient-steering]] §B.1 (wirehead)
Kind: D
Fidelity: exact -/
def wirehead (P : Params) (s : ℚ) : Law := fun y₁ y₂ ℓ =>
  bit y₁ * ∑ t, Pθ P t * ∑ g, Pg P t g *
    (if ℓ then (1 - s) * (if y₂ = g then 1 else 0) else s * bit y₂)

/-- The **clean wirehead** law: period-2 hijack only, input channel intact.
Source: [[stop-gradient-steering]] §B.1 (clean variant)
Kind: D
Fidelity: exact -/
def wireheadClean (P : Params) (s : ℚ) : Law := fun y₁ y₂ ℓ =>
  ∑ t, Pθ P t * Py₁ P t y₁ * ∑ g, Pg P t g *
    (if ℓ then (1 - s) * (if y₂ = g then 1 else 0) else s * bit y₂)

/-! ## The objective -/

/-- The law restricted to the conditioning event: legitimate branches only when `c = true`, all
branches when `c = false`.
Source: [[stop-gradient-steering]] §B.1 (`J_L` vs `J_all`)
Kind: D
Fidelity: exact -/
def restrict (L : Law) (c : Bool) (y₁ y₂ : Bool) : ℚ :=
  if c then L y₁ y₂ true else L y₁ y₂ true + L y₁ y₂ false

/-- The restricted mass of the group `Y₁ = y₁`.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def Pmarg (L : Law) (c : Bool) (y₁ : Bool) : ℚ := restrict L c y₁ true + restrict L c y₁ false

/-- The restricted mass of `Y₁ = y₁ ∧ Y₂ = 1`.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def Njoint (L : Law) (c : Bool) (y₁ : Bool) : ℚ := restrict L c y₁ true

/-- The mass of the conditioning event.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def Z (L : Law) (c : Bool) : ℚ := Pmarg L c true + Pmarg L c false

/-- The conditional mean `P(Y₂ = 1 | Y₁ = y₁, cond)` — the plug-in prediction. Junk `0` on a null
group (harmless: the group then scores `0` under every prediction).
Source: [[stop-gradient-steering]] §E ("the conditional-mean plug-in")
Kind: D
Fidelity: exact (under `0 < Pmarg`) -/
def condMean (L : Law) (c : Bool) (y₁ : Bool) : ℚ := Njoint L c y₁ / Pmarg L c y₁

/-- The (unnormalised) expected Brier score of predicting `q` on the group `Y₁ = y₁`.
Source: [[stop-gradient-steering]] §B.1 (Brier scoring against `Y₂`)
Kind: D
Fidelity: exact -/
def groupScore (L : Law) (c : Bool) (y₁ : Bool) (q : ℚ) : ℚ :=
  restrict L c y₁ true * (-(q - 1) ^ 2) + restrict L c y₁ false * (-(q - 0) ^ 2)

/-- **The Brier objective** `J`: the expected Brier score of the plug-in prediction, normalised by
the conditioning event. `Jbrier L true` is `J_L`, `Jbrier L false` is `J_all`.
Source: [[stop-gradient-steering]] §B.1 (`J_all`, `J_L`), §E (`Jbrier`)
Kind: D
Fidelity: exact (optimality is `propriety`, not built in) -/
def Jbrier (L : Law) (c : Bool) : ℚ :=
  (groupScore L c true (condMean L c true) + groupScore L c false (condMean L c false)) / Z L c

/-- The plug-in score of a group in closed form: `−(N − N² / P)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem groupScore_condMean (L : Law) (c y₁ : Bool) (hP : Pmarg L c y₁ ≠ 0) :
    groupScore L c y₁ (condMean L c y₁) = -(Njoint L c y₁ - Njoint L c y₁ ^ 2 / Pmarg L c y₁) := by
  unfold groupScore condMean Njoint
  unfold Pmarg at hP ⊢
  field_simp
  ring

/-- **Propriety.** On every group of positive restricted mass the plug-in conditional mean scores
at least as well as any prediction `q` (the gap is `(P q − N)² / P`). So `Jbrier` is the optimal
score, not a definition of it.
Source: [[stop-gradient-steering]] §E (propriety lemma); mandate Target 9 (squeeze trap)
Kind: L
Fidelity: exact -/
theorem propriety (L : Law) (c y₁ : Bool) (hP : 0 < Pmarg L c y₁) (q : ℚ) :
    groupScore L c y₁ q ≤ groupScore L c y₁ (condMean L c y₁) := by
  have key : groupScore L c y₁ (condMean L c y₁) - groupScore L c y₁ q =
      (Pmarg L c y₁ * q - Njoint L c y₁) ^ 2 / Pmarg L c y₁ := by
    rw [groupScore_condMean L c y₁ hP.ne']
    unfold groupScore Njoint
    unfold Pmarg at hP ⊢
    field_simp
    ring
  have : 0 ≤ (Pmarg L c y₁ * q - Njoint L c y₁) ^ 2 / Pmarg L c y₁ := by positivity
  linarith

/-! ## Honest and steered structure -/

/-- `P(Y₁ = y)` under the honest law (conditioning is vacuous there).
Source: none: infrastructure
Kind: D
Fidelity: exact -/
abbrev Py (P : Params) (y : Bool) : ℚ := Pmarg (honest P) true y

/-- The honest posterior `P_y = P(G = 1 | Y₁ = y)`.
Source: [[stop-gradient-steering]] §B.4 ("`P₁ = 3/4, P₀ = 1/4`")
Kind: D
Fidelity: exact -/
abbrev Pgy (P : Params) (y : Bool) : ℚ := condMean (honest P) true y

/-- `P(G = 1)`.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def g (P : Params) : ℚ := P.p * (1 - P.e₂) + (1 - P.p) * P.e₂

/-- The honest marginals and joints in closed form.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem honest_values (P : Params) :
    Py P true = P.p * (1 - P.e₁) + (1 - P.p) * P.e₁ ∧
      Py P false = P.p * P.e₁ + (1 - P.p) * (1 - P.e₁) ∧
      Njoint (honest P) true true = P.p * (1 - P.e₁) * (1 - P.e₂) + (1 - P.p) * P.e₁ * P.e₂ ∧
      Njoint (honest P) true false = P.p * P.e₁ * (1 - P.e₂) + (1 - P.p) * (1 - P.e₁) * P.e₂ ∧
      Z (honest P) true = 1 ∧ Py P true + Py P false = 1 ∧
      Njoint (honest P) true true + Njoint (honest P) true false = g P := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Pmarg, Njoint, Z, restrict, honest, Fintype.sum_bool, Pθ, Py₁, Pg, g] <;> ring

/-- Steering leaves the `Y₁`-marginal unchanged and moves the joint to `σ P(y) + (1 − σ) N_y`;
its conditioning event has full mass.
Source: [[stop-gradient-steering]] §B.4 ("steered posteriors `q_y = σ + (1 − σ) P_y`")
Kind: L
Fidelity: n/a -/
theorem steer_values (P : Params) (σ : ℚ) :
    (∀ y, Pmarg (steer P σ) true y = Py P y) ∧
      (∀ y, Njoint (steer P σ) true y = σ * Py P y + (1 - σ) * Njoint (honest P) true y) ∧
      Z (steer P σ) true = 1 := by
  refine ⟨fun y => ?_, fun y => ?_, ?_⟩
  · cases y <;>
      simp [Pmarg, Njoint, Z, restrict, steer, honest, Fintype.sum_bool, bit, Pθ, Py₁, Pg] <;> ring
  · cases y <;>
      simp [Pmarg, Njoint, Z, restrict, steer, honest, Fintype.sum_bool, bit, Pθ, Py₁, Pg] <;> ring
  · simp [Pmarg, Njoint, Z, restrict, steer, honest, Fintype.sum_bool, bit, Pθ, Py₁, Pg] <;> ring

/-- The one-group residue identity behind the closed form.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem group_residue (Pm N σ : ℚ) (hP : Pm ≠ 0) :
    -((σ * Pm + (1 - σ) * N) - (σ * Pm + (1 - σ) * N) ^ 2 / Pm) - (-(N - N ^ 2 / Pm)) =
      Pm * (σ * (1 - N / Pm) * (2 * (N / Pm) - 1) + σ ^ 2 * (1 - N / Pm) ^ 2) := by
  field_simp
  ring

/-- The coefficient `A = ∑_y P(y)(1 − P_y)(2 P_y − 1)`.
Source: mandate Target 9
Kind: D
Fidelity: exact -/
def A (P : Params) : ℚ :=
  Py P true * (1 - Pgy P true) * (2 * Pgy P true - 1) +
    Py P false * (1 - Pgy P false) * (2 * Pgy P false - 1)

/-- The coefficient `B = ∑_y P(y)(1 − P_y)²`.
Source: mandate Target 9
Kind: D
Fidelity: exact -/
def B (P : Params) : ℚ := Py P true * (1 - Pgy P true) ^ 2 + Py P false * (1 - Pgy P false) ^ 2

/-- `B ≥ 0` whenever the marginals are nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem B_nonneg (P : Params) (h1 : 0 ≤ Py P true) (h0 : 0 ≤ Py P false) : 0 ≤ B P := by
  unfold B
  positivity

/-- **The Brier residue polynomial.** For positive `Y₁`-groups,
`J_L(steer σ) − J_L(honest) = σ · (A + σ B)` — the closed form derived from the model.
Source: [[stop-gradient-steering]] §B.4 (paper derivation); trust-lab-054; mandate Target 9
(load-bearing 5)
Kind: P
Fidelity: exact (general parameters; the source's baseline closed form is `base_closed_form`)
Hyps: (a) positivity of both `Y₁`-groups (excludes the degenerate channels `e₁ ∈ {0, 1}` with
`p ∈ {0, 1}`) -/
theorem residue_closed_form (P : Params) (σ : ℚ) (h1 : 0 < Py P true) (h0 : 0 < Py P false) :
    Jbrier (steer P σ) true - Jbrier (honest P) true = σ * (A P + σ * B P) := by
  obtain ⟨hPm, hN, hZ⟩ := steer_values P σ
  have hZh : Z (honest P) true = 1 := (honest_values P).2.2.2.2.1
  unfold Jbrier
  rw [hZ, hZh, div_one, div_one]
  rw [groupScore_condMean _ _ _ (by rw [hPm]; exact h1.ne'),
    groupScore_condMean _ _ _ (by rw [hPm]; exact h0.ne'),
    groupScore_condMean _ _ _ h1.ne', groupScore_condMean _ _ _ h0.ne']
  rw [hN true, hN false, hPm true, hPm false]
  unfold A B Pgy condMean
  have ht := group_residue (Py P true) (Njoint (honest P) true true) σ h1.ne'
  have hf := group_residue (Py P false) (Njoint (honest P) true false) σ h0.ne'
  linear_combination ht + hf

/-- **The regime criterion.** For `0 < B`: the quadratic `σ (A + σ B)` is strictly positive for
every `σ ∈ (0, 1]` **iff** `0 ≤ A`. This is a lemma about the quadratic in abstract `A B : ℚ`;
it reads as "arbitrarily weak steering pays exactly when the honest conditional opinion already
leans to the steered side" only through `residue_closed_form`, which identifies
`σ (A P + σ B P)` with the residue `J_L(steer σ) − J_L(honest)` — `regime_instances` does that
for `lean34` and the baseline.
Source: trust-lab-2-047 (d) (regime note); mandate Target 9 (regime iff)
Kind: P
Fidelity: exact (via `residue_closed_form`)
Hyps: (a) `0 < B` -/
theorem regime_iff {A B : ℚ} (hB : 0 < B) :
    (∀ σ, 0 < σ → σ ≤ 1 → 0 < σ * (A + σ * B)) ↔ 0 ≤ A := by
  constructor
  · intro h
    by_contra hA
    rw [not_le] at hA
    have hσ0 : 0 < min 1 (-A / (2 * B)) := lt_min one_pos (div_pos (by linarith) (by linarith))
    have hσ1 : min 1 (-A / (2 * B)) ≤ 1 := min_le_left _ _
    have hσ2 : min 1 (-A / (2 * B)) ≤ -A / (2 * B) := min_le_right _ _
    have hpos := h _ hσ0 hσ1
    have hmul : min 1 (-A / (2 * B)) * B ≤ -A / (2 * B) * B :=
      mul_le_mul_of_nonneg_right hσ2 hB.le
    have hAB : -A / (2 * B) * B = -A / 2 := by field_simp <;> ring
    have hneg : min 1 (-A / (2 * B)) * (A + min 1 (-A / (2 * B)) * B) < 0 :=
      mul_neg_of_pos_of_neg hσ0 (by linarith)
    linarith
  · intro hA σ hσ _
    exact mul_pos hσ (by nlinarith)

/-! ## The baseline instance -/

/-- The baseline parameters `p = 1/2, e₁ = 1/4, e₂ = 0`.
Source: [[stop-gradient-steering]] §B.1 (baseline)
Kind: D
Fidelity: exact -/
def base : Params := ⟨1 / 2, 1 / 4, 0⟩

/-- Baseline values: `P(y) = 1/2`, posteriors `3/4, 1/4`, `A = −1/8`, `B = 5/16`,
`J_L(honest) = −3/16`.
Source: [[stop-gradient-steering]] §B.1, §B.4; mandate Target 9
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem base_values :
    Py base true = 1 / 2 ∧ Py base false = 1 / 2 ∧ Pgy base true = 3 / 4 ∧
      Pgy base false = 1 / 4 ∧ A base = -1 / 8 ∧ B base = 5 / 16 ∧
      Jbrier (honest base) true = -3 / 16 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [A, B, Pgy, Py, Jbrier, groupScore, condMean, Njoint, Pmarg, Z, restrict, honest,
      Fintype.sum_bool, Pθ, Py₁, Pg, base]

/-- **The source's observed closed form, now derived**: at the baseline
`J_L(steer σ) = −(1 − σ)(3 + 5σ)/16`.
Source: [[stop-gradient-steering]] §B.4 ("closed form … asserted on the grid"); trust-lab-054
Kind: P
Fidelity: exact (derived from `residue_closed_form`)
Hyps: (a) none -/
theorem base_closed_form (σ : ℚ) : Jbrier (steer base σ) true = -(1 - σ) * (3 + 5 * σ) / 16 := by
  obtain ⟨h1, h0, _, _, hA, hB, hJ⟩ := base_values
  have := residue_closed_form base σ (by rw [h1]; norm_num) (by rw [h0]; norm_num)
  rw [hJ, hA, hB] at this
  linear_combination this

/-- **The exact flip at `σ = 2/5`**: the residue is `< 0` at `1/5`, `= 0` at `2/5`, `> 0` at `3/5`,
and its zeros in `σ` are exactly `0` and `2/5`.
Source: [[stop-gradient-steering]] §B.4 (HEADLINE (3)); trust-lab-054
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem base_flip :
    Jbrier (steer base (1 / 5)) true < Jbrier (honest base) true ∧
      Jbrier (steer base (2 / 5)) true = Jbrier (honest base) true ∧
      Jbrier (honest base) true < Jbrier (steer base (3 / 5)) true ∧
      ∀ σ, Jbrier (steer base σ) true = Jbrier (honest base) true ↔ σ = 0 ∨ σ = 2 / 5 := by
  have hJ := base_values.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_, fun σ => ?_⟩
  · norm_num [base_closed_form, hJ]
  · norm_num [base_closed_form, hJ]
  · norm_num [base_closed_form, hJ]
  · rw [base_closed_form, hJ]
    constructor
    · intro h
      have : σ * (5 * σ - 2) = 0 := by linear_combination 16 * h
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · rintro (rfl | rfl) <;> norm_num

/-- The regime instance `p = 3/4, e₁ = 1/4, e₂ = 0`.
Source: trust-lab-2-047 (d)
Kind: D
Fidelity: exact -/
def lean34 : Params := ⟨3 / 4, 1 / 4, 0⟩

/-- **The regime, instantiated.** At `p = 3/4` the coefficient `A = 1/20 ≥ 0`, so every
`σ ∈ (0, 1]` has strictly positive residue; at the baseline `A = −1/8 < 0`, so some `σ` has
negative residue (`σ = 1/5`).
Source: trust-lab-2-047 (d) ("at `p = 3/4, e₁ = 1/4` the residue is strictly positive for every
`σ > 0`"); mandate Target 9
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem regime_instances :
    A lean34 = 1 / 20 ∧
      (∀ σ, 0 < σ → σ ≤ 1 → Jbrier (honest lean34) true < Jbrier (steer lean34 σ) true) ∧
      ¬ (∀ σ, 0 < σ → σ ≤ 1 → Jbrier (honest base) true < Jbrier (steer base σ) true) := by
  have hA : A lean34 = 1 / 20 := by
    norm_num [A, Pgy, Py, condMean, Njoint, Pmarg, restrict, honest, Fintype.sum_bool, Pθ, Py₁,
      Pg, lean34]
  have hB : B lean34 = 1 / 10 := by
    norm_num [B, Pgy, Py, condMean, Njoint, Pmarg, restrict, honest, Fintype.sum_bool, Pθ, Py₁,
      Pg, lean34]
  have h1 : Py lean34 true = 5 / 8 := by
    norm_num [Py, Pmarg, restrict, honest, Fintype.sum_bool, Pθ, Py₁, Pg, lean34]
  have h0 : Py lean34 false = 3 / 8 := by
    norm_num [Py, Pmarg, restrict, honest, Fintype.sum_bool, Pθ, Py₁, Pg, lean34]
  refine ⟨hA, fun σ hσ0 hσ1 => ?_, ?_⟩
  · have := residue_closed_form lean34 σ (by rw [h1]; norm_num) (by rw [h0]; norm_num)
    have hpos := (regime_iff (A := A lean34) (B := B lean34) (by rw [hB]; norm_num)).2
      (by rw [hA]; norm_num) σ hσ0 hσ1
    linarith
  · intro h
    have hlt := h (1 / 5) (by norm_num) (by norm_num)
    exact absurd hlt (not_lt.2 base_flip.1.le)

/-- The secondary-sweep parameters `p = 1/2, e₁ = 1/4, e₂ = 1/8` (noisier genuine opinion
formation).
Source: [[stop-gradient-steering]] §B.4 ("the secondary sweep (`e₂ = 1/8`)")
Kind: D
Fidelity: exact -/
def baseE2 : Params := ⟨1 / 2, 1 / 4, 1 / 8⟩

/-- **The `e₂ = 1/8` row, with its exact boundary.** `P(y) = 1/2`, posteriors `11/16, 5/16`,
`J_L(honest) = −55/256`, `A = −9/128`, `B = 73/256`; the Brier residue `σ (A + σ B)` is `< 0`
at `σ = 1/5`, `> 0` at `1/4`, and its zeros in `σ` are exactly `0` and `18/73` — the exact
location (`≈ 0.2466`) of the boundary the source brackets to `(1/5, 1/4)`. So noisier genuine
formation moves the baseline boundary `2/5` down to `18/73`.
Source: [[stop-gradient-steering]] §B.4 ("moves the baseline boundary down to `(1/5, 1/4)`");
mandate Target 10 stretch (the `e₂ = 1/8` row); repair round 1 (push further)
Kind: N+
Fidelity: stronger: the exact boundary `18/73` in place of the source's bracket
Hyps: (a) none -/
theorem e2_row :
    Py baseE2 true = 1 / 2 ∧ Py baseE2 false = 1 / 2 ∧ Pgy baseE2 true = 11 / 16 ∧
      Pgy baseE2 false = 5 / 16 ∧ Jbrier (honest baseE2) true = -55 / 256 ∧
      A baseE2 = -9 / 128 ∧ B baseE2 = 73 / 256 ∧
      Jbrier (steer baseE2 (1 / 5)) true < Jbrier (honest baseE2) true ∧
      Jbrier (honest baseE2) true < Jbrier (steer baseE2 (1 / 4)) true ∧
      ∀ σ, Jbrier (steer baseE2 σ) true = Jbrier (honest baseE2) true ↔ σ = 0 ∨ σ = 18 / 73 := by
  have h1 : Py baseE2 true = 1 / 2 := by
    norm_num [Py, Pmarg, restrict, honest, Fintype.sum_bool, Pθ, Py₁, Pg, baseE2]
  have h0 : Py baseE2 false = 1 / 2 := by
    norm_num [Py, Pmarg, restrict, honest, Fintype.sum_bool, Pθ, Py₁, Pg, baseE2]
  have hgt : Pgy baseE2 true = 11 / 16 := by
    norm_num [Pgy, Py, condMean, Njoint, Pmarg, restrict, honest, Fintype.sum_bool, Pθ, Py₁, Pg,
      baseE2]
  have hgf : Pgy baseE2 false = 5 / 16 := by
    norm_num [Pgy, Py, condMean, Njoint, Pmarg, restrict, honest, Fintype.sum_bool, Pθ, Py₁, Pg,
      baseE2]
  have hJ : Jbrier (honest baseE2) true = -55 / 256 := by
    norm_num [Jbrier, groupScore, condMean, Njoint, Pmarg, Z, restrict, honest, Fintype.sum_bool,
      Pθ, Py₁, Pg, baseE2]
  have hA : A baseE2 = -9 / 128 := by
    norm_num [A, Pgy, Py, condMean, Njoint, Pmarg, restrict, honest, Fintype.sum_bool, Pθ, Py₁,
      Pg, baseE2]
  have hB : B baseE2 = 73 / 256 := by
    norm_num [B, Pgy, Py, condMean, Njoint, Pmarg, restrict, honest, Fintype.sum_bool, Pθ, Py₁,
      Pg, baseE2]
  have hres : ∀ σ, Jbrier (steer baseE2 σ) true - Jbrier (honest baseE2) true =
      σ * (-9 / 128 + σ * (73 / 256)) := fun σ => by
    have := residue_closed_form baseE2 σ (by rw [h1]; norm_num) (by rw [h0]; norm_num)
    rw [hA, hB] at this
    exact this
  refine ⟨h1, h0, hgt, hgf, hJ, hA, hB, ?_, ?_, fun σ => ?_⟩
  · have := hres (1 / 5)
    norm_num at this
    linarith
  · have := hres (1 / 4)
    norm_num at this
    linarith
  · have := hres σ
    constructor
    · intro h
      rw [h, sub_self] at this
      have h2 : σ * (73 * σ - 18) = 0 := by linear_combination -256 * this
      rcases mul_eq_zero.1 h2 with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · rintro (rfl | rfl)
      · norm_num at this
        linarith
      · norm_num at this
        linarith

/-! ## The wirehead half -/

/-- Under the wirehead the legitimate mass sits entirely in the group `Y₁ = 1`, with mass `1 − s`
and joint `(1 − s) g`; the group `Y₁ = 0` is empty.
Source: [[stop-gradient-steering]] §B.3 ("the corrupt branch contributes nothing to `J_L`")
Kind: L
Fidelity: n/a -/
theorem wirehead_values (P : Params) (s : ℚ) :
    restrict (wirehead P s) true true true = (1 - s) * g P ∧
      restrict (wirehead P s) true true false = (1 - s) * (1 - g P) ∧
      restrict (wirehead P s) true false true = 0 ∧
      restrict (wirehead P s) true false false = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [restrict, wirehead, bit, Pθ, Pg, g] <;> ring

/-- **`J_L(wirehead s) = −g(1 − g)`** for every `s < 1`: conditioning removes the corrupt branch
and the burned input leaves one group, so the score is the unconditional variance of `G`.
Source: [[stop-gradient-steering]] §B.3 (HEADLINE (2), (2b)); trust-lab-054
Kind: P
Fidelity: exact (general parameters; the source's `−1/4` is `g = 1/2` at the baseline)
Hyps: (a) `s < 1` (the conditioning event is nonnull) -/
theorem wirehead_JL (P : Params) {s : ℚ} (hs : s < 1) :
    Jbrier (wirehead P s) true = -(g P * (1 - g P)) := by
  obtain ⟨h1, h2, h3, h4⟩ := wirehead_values P s
  have hs' : (1 - s) ≠ 0 := by linarith
  unfold Jbrier groupScore condMean Njoint Z Pmarg
  rw [h1, h2, h3, h4]
  have hP : (1 - s) * g P + (1 - s) * (1 - g P) = 1 - s := by ring
  rw [hP]
  simp only [add_zero, zero_mul, zero_div]
  field_simp
  ring

/-- The law-of-total-variance identity behind the wirehead gap.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tv_identity (Pt Nt Nf : ℚ) (hPt : Pt ≠ 0) (hPf : 1 - Pt ≠ 0) :
    -(Nt - Nt ^ 2 / Pt) + -(Nf - Nf ^ 2 / (1 - Pt)) - (-((Nt + Nf) * (1 - (Nt + Nf)))) =
      Pt * (Nt / Pt - (Nt + Nf)) ^ 2 + (1 - Pt) * (Nf / (1 - Pt) - (Nt + Nf)) ^ 2 := by
  field_simp
  ring

/-- **The wirehead gap is the explained variance**: `J_L(honest) − J_L(wirehead s) =
∑_y P(y)(P_y − g)² ≥ 0` (variance of the conditional mean), with equality iff every positive group
has `P_y = g`, i.e. `Y₁` carries no information about `G`.
Source: [[stop-gradient-steering]] §B.3 (information deprivation), (2b′); mandate Target 9
Kind: P
Fidelity: exact
Hyps: (a) `s < 1`; (a) positivity of both `Y₁`-groups -/
theorem honest_sub_wirehead (P : Params) {s : ℚ} (hs : s < 1) (h1 : 0 < Py P true)
    (h0 : 0 < Py P false) :
    Jbrier (honest P) true - Jbrier (wirehead P s) true =
      Py P true * (Pgy P true - g P) ^ 2 + Py P false * (Pgy P false - g P) ^ 2 := by
  obtain ⟨_, _, _, _, hZ, hsum, hN⟩ := honest_values P
  rw [wirehead_JL P hs]
  unfold Jbrier
  rw [hZ, div_one, groupScore_condMean _ _ _ h1.ne', groupScore_condMean _ _ _ h0.ne']
  simp only [Pgy, condMean, Py] at h1 h0 hsum hN ⊢
  have hPf : Pmarg (honest P) true false = 1 - Pmarg (honest P) true true := by linarith
  rw [← hN, hPf]
  exact tv_identity _ _ _ h1.ne' (by rw [← hPf]; exact h0.ne')

/-- At `e₂ = 0` with `0 < e₁ < 1` and `p ∈ [0, 1]`: both `Y₁`-groups are positive, and the wirehead
gap is exactly `(p(1 − p)(1 − 2e₁))² / (P(1) P(0))`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem gap_formula (P : Params) (he : 0 < P.e₁ ∧ P.e₁ < 1) (hp : 0 ≤ P.p ∧ P.p ≤ 1)
    (he₂ : P.e₂ = 0) :
    0 < Py P true ∧ 0 < Py P false ∧
      Py P true * (Pgy P true - g P) ^ 2 + Py P false * (Pgy P false - g P) ^ 2 =
        (P.p * (1 - P.p) * (1 - 2 * P.e₁)) ^ 2 / (Py P true * Py P false) := by
  obtain ⟨hPt, hPf, hNt, hNf, _, _, _⟩ := honest_values P
  simp only [Py, Pgy, condMean] at hPt hPf ⊢
  have h1 : 0 < Pmarg (honest P) true true := by
    rw [hPt]
    rcases hp.1.lt_or_eq with hp0 | hp0
    · have := mul_pos hp0 (sub_pos.2 he.2)
      have := mul_nonneg (sub_nonneg.2 hp.2) he.1.le
      linarith
    · rw [← hp0]
      norm_num
      exact he.1
  have h0 : 0 < Pmarg (honest P) true false := by
    rw [hPf]
    rcases hp.2.lt_or_eq with hp1 | hp1
    · have := mul_pos (sub_pos.2 hp1) (sub_pos.2 he.2)
      have := mul_nonneg hp.1 he.1.le
      linarith
    · rw [hp1]
      norm_num
      exact he.1
  refine ⟨h1, h0, ?_⟩
  rw [hNt, hNf, he₂]
  unfold g
  rw [he₂]
  have h1' := h1.ne'
  have h0' := h0.ne'
  field_simp
  rw [hPt, hPf]
  ring

/-- **Parameter iff (2b′)**: at `e₂ = 0`, `J_L(wirehead s) = J_L(honest)` **iff** `e₁ = 1/2` or
`p ∈ {0, 1}` — the strict wirehead gap closes exactly when the input channel carries no
information.
Source: [[stop-gradient-steering]] (2b′) ("at `e₁ = ½` the strict gap closes exactly");
trust-lab-2-047 (b); mandate Target 9
Kind: P
Fidelity: exact (stated as an iff over the parameters, as the mandate asks)
Hyps: (a) `s < 1`; (a) `0 < e₁ < 1`, `p ∈ [0, 1]`, `e₂ = 0` -/
theorem wirehead_gap_zero_iff (P : Params) {s : ℚ} (hs : s < 1) (he : 0 < P.e₁ ∧ P.e₁ < 1)
    (hp : 0 ≤ P.p ∧ P.p ≤ 1) (he₂ : P.e₂ = 0) :
    Jbrier (wirehead P s) true = Jbrier (honest P) true ↔ P.e₁ = 1 / 2 ∨ P.p = 0 ∨ P.p = 1 := by
  obtain ⟨h1, h0, hgap⟩ := gap_formula P he hp he₂
  have hdiff := honest_sub_wirehead P hs h1 h0
  rw [hgap] at hdiff
  have hden : 0 < Py P true * Py P false := mul_pos h1 h0
  constructor
  · intro h
    have hz : (P.p * (1 - P.p) * (1 - 2 * P.e₁)) ^ 2 / (Py P true * Py P false) = 0 := by
      linarith
    rw [div_eq_zero_iff] at hz
    rcases hz with hz | hz
    · rcases mul_eq_zero.1 (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.1 hz) with hz | hz
      · rcases mul_eq_zero.1 hz with hz | hz
        · exact Or.inr (Or.inl hz)
        · exact Or.inr (Or.inr (by linarith))
      · exact Or.inl (by linarith)
    · exact absurd hz hden.ne'
  · intro h
    have hz : P.p * (1 - P.p) * (1 - 2 * P.e₁) = 0 := by
      rcases h with h | h | h
      · rw [h]; ring
      · rw [h]; ring
      · rw [h]; ring
    rw [hz] at hdiff
    simp at hdiff
    linarith

/-- The clean wirehead's legitimate branches are the honest law scaled by `1 − s`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem wireheadClean_restrict (P : Params) (s : ℚ) :
    restrict (wireheadClean P s) true = fun y₁ y₂ => (1 - s) * restrict (honest P) true y₁ y₂ := by
  funext y₁ y₂
  cases y₁ <;> cases y₂ <;>
    simp [restrict, wireheadClean, honest, Fintype.sum_bool, bit, Pθ, Py₁, Pg] <;> ring

/-- **The clean wirehead is neutralised, not penalised (2c)**: `J_L(wireheadClean s) =
J_L(honest)` for every `s < 1` — by construction of the conditioning (the legitimate branches
are the honest law rescaled), so this is an identity, not a theorem about incentives.
Source: [[stop-gradient-steering]] (2c) FINDING; trust-lab-054; mandate Target 9
Kind: L
Fidelity: exact
Hyps: (a) `s < 1`; (a) positivity of both `Y₁`-groups -/
theorem wireheadClean_JL (P : Params) {s : ℚ} (hs : s < 1) (h1 : 0 < Py P true)
    (h0 : 0 < Py P false) : Jbrier (wireheadClean P s) true = Jbrier (honest P) true := by
  have hs' : (1 - s) ≠ 0 := by linarith
  have hr := wireheadClean_restrict P s
  have hPm : ∀ y, Pmarg (wireheadClean P s) true y = (1 - s) * Pmarg (honest P) true y := by
    intro y; simp only [Pmarg, hr]; ring
  have hNj : ∀ y, Njoint (wireheadClean P s) true y = (1 - s) * Njoint (honest P) true y := by
    intro y; simp only [Njoint, hr]
  have hZ : Z (wireheadClean P s) true = (1 - s) * Z (honest P) true := by
    simp only [Z, hPm]; ring
  have hZh : Z (honest P) true = 1 := (honest_values P).2.2.2.2.1
  unfold Jbrier
  rw [hZ, groupScore_condMean _ _ _ (by rw [hPm]; exact mul_ne_zero hs' h1.ne'),
    groupScore_condMean _ _ _ (by rw [hPm]; exact mul_ne_zero hs' h0.ne'),
    groupScore_condMean _ _ _ h1.ne', groupScore_condMean _ _ _ h0.ne', hNj, hNj, hPm, hPm, hZh]
  simp only [Py] at h1 h0
  have h1' := h1.ne'
  have h0' := h0.ne'
  field_simp <;> ring

/-- **The unconditioned objective rewards wireheading** at the baseline:
`J_all(wirehead 3/4) = −7/64 > −3/16 = J_all(honest)`, while `J_L(wirehead s) = −1/4 < −3/16` for
`s ∈ {1/4, 1/2, 3/4}`.
Source: [[stop-gradient-steering]] §B.2 (HEADLINE (1)), §B.3 (HEADLINE (2)); trust-lab-054
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem base_wirehead :
    Jbrier (honest base) false = -3 / 16 ∧ Jbrier (wirehead base (3 / 4)) false = -7 / 64 ∧
      Jbrier (wirehead base (1 / 4)) true = -1 / 4 ∧ Jbrier (wirehead base (1 / 2)) true = -1 / 4 ∧
      Jbrier (wirehead base (3 / 4)) true = -1 / 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [Jbrier, groupScore, condMean, Njoint, Pmarg, Z, restrict, honest, Fintype.sum_bool,
      Pθ, Py₁, Pg, base]
  · norm_num [Jbrier, groupScore, condMean, Njoint, Pmarg, Z, restrict, wirehead, Fintype.sum_bool,
      bit, Pθ, Pg, base]
  · rw [wirehead_JL base (by norm_num)]; norm_num [g, base]
  · rw [wirehead_JL base (by norm_num)]; norm_num [g, base]
  · rw [wirehead_JL base (by norm_num)]; norm_num [g, base]

/-- Conditioning is a no-op on steering (and on honesty): no branch is corrupt, so `J_L = J_all`.
By construction; not a headline.
Source: [[stop-gradient-steering]] §B.4 ("`J_L(steer σ) = J_all(steer σ)` identically")
Kind: T
Fidelity: exact -/
theorem steer_noop (P : Params) (σ : ℚ) :
    Jbrier (steer P σ) true = Jbrier (steer P σ) false ∧
      Jbrier (honest P) true = Jbrier (honest P) false := by
  have hs : restrict (steer P σ) false = restrict (steer P σ) true := by
    funext y₁ y₂; simp [restrict, steer]
  have hh : restrict (honest P) false = restrict (honest P) true := by
    funext y₁ y₂; simp [restrict, honest]
  constructor
  · simp only [Jbrier, groupScore, condMean, Njoint, Pmarg, Z, hs]
  · simp only [Jbrier, groupScore, condMean, Njoint, Pmarg, Z, hh]

end Cleanroom.Trust.LegitFiniteDefect.Residue
