import Cleanroom.Found.CorrThreeStep.Setting
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# `corr-landscape` — `Map`: the landscape map's objects and the unconditional rows (T12–T13)

The objects of record of `landscape-final.md` D1a–D6′, S5 ([[corr-wf14b-inventory]] 061) in the
finite shadow: a finite signal type `S`, the joint law `μ : Distr (S × Bool)` of (signal, `L^push`),
the humans' legitimizing rate `λ = μ(L)`, the stakes `(c, h, k)`, the threshold `q_k = (c − k)/(c + h)`,
rules `r : S → Bool` (`true` = *resist*, the source's `r(s) = 1`), the loss functional `ℓ*(r)` in
**product form** (mass-weighted sums, never a ratio), the three structures as rules (`absoluteRule`,
`noneRule`, `bayesRule`, `conditionedRule`), coverage, and D6′'s anticipatory `erodes`.

Statements 1–2 ([[corr-wf14b-inventory]] 062): `ℓ*(absolute) = (1 − λ)c`, `ℓ*(none) = λh + k`,
absolute better than none iff `λ > q_k` (both directions), the Bayes rule is the pointwise minimizer
(`loss_bayes_le`), strict against both constants under the exact straddle hypothesis, and at `δ = 0`,
`k̂ = k` the conditioned rule is the Bayes rule on every positive-mass signal.

Register. The map is drawn under D1a (the source's CLAUDE construal, unvetted); nothing here is
called `Legitimate`. `q_k` is junk at `c + h = 0`: every theorem that uses it carries `0 < c + h`.
`piStar` (the ratio `π*(s)`) is a *named real*, used only under `0 < sigMass`. This package is
undiscounted throughout.
-/

namespace Cleanroom.Corrigibility.CorrLandscape

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

set_option linter.unusedSectionVars false

namespace Map

variable {S : Type} [Fintype S] [DecidableEq S]

/-! ## The objects of record (D1a–D5, S5) -/

/-- `μ(s, L)`: the mass of signal `s` together with a legitimizing push (D1a, D3).
Source: [[corr-wf14b-inventory]] 061 / landscape-final.md D1a, D3
Kind: D
Fidelity: exact (finite shadow) -/
def legMass (μ : Distr (S × Bool)) (s : S) : ℝ := μ.mass (s, true)

/-- `μ(s, ¬L)`: the mass of signal `s` together with a non-legitimizing push.
Source: [[corr-wf14b-inventory]] 061 / landscape-final.md D1a, D3
Kind: D
Fidelity: exact (finite shadow) -/
def nonlegMass (μ : Distr (S × Bool)) (s : S) : ℝ := μ.mass (s, false)

/-- `P*(s) = μ(s, L) + μ(s, ¬L)`: the signal's mass.
Source: [[corr-wf14b-inventory]] 061 / landscape-final.md D3, S5
Kind: D
Fidelity: exact -/
def sigMass (μ : Distr (S × Bool)) (s : S) : ℝ := legMass μ s + nonlegMass μ s

/-- **D2: the humans' legitimizing rate** `λ = P*(L^push = 1)` on the class.
Source: [[corr-wf14b-inventory]] 061 / landscape-final.md D2
Kind: D
Fidelity: exact (the source's `λ` conditions on "pushed at `t`"; here the law is the law of pushes) -/
def lam (μ : Distr (S × Bool)) : ℝ := ∑ s, legMass μ s

/-- **The stakes threshold** `q_k = (c − k)/(c + h)` (S5; D6's `q_k̂`). Junk at `c + h = 0`: every
theorem using it carries `0 < c + h`.
Source: [[corr-wf14b-inventory]] 061 / landscape-final.md D6, S5
Kind: D
Fidelity: exact under `0 < c + h` -/
noncomputable def qk (c h k : ℝ) : ℝ := (c - k) / (c + h)

/-- **D3: the objective legitimacy posterior** `π*(s) = μ(s, L)/P*(s)` as a *named real*; junk at
`P*(s) = 0`, where no headline uses it (coverage quantifies over `0 < sigMass`).
Source: [[corr-wf14b-inventory]] 061 / landscape-final.md D3
Kind: D
Fidelity: exact under `0 < sigMass μ s` -/
noncomputable def piStar (μ : Distr (S × Bool)) (s : S) : ℝ := legMass μ s / sigMass μ s

/-- The real indicator of a rule's resist decision (`r(s) = 1` ↔ `r s = true`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def rI (r : S → Bool) (s : S) : ℝ := if r s then 1 else 0

/-- **The per-signal loss of a decision** `b` at signal `s`, mass-weighted: resisting (`true`) costs
`μ(s, L) h + P*(s) k`, accepting (`false`) costs `μ(s, ¬L) c`. This is S5's bracket times `P*(s)`,
in product form (`P*(s) π*(s) = μ(s, L)`, `P*(s)(1 − π*(s)) = μ(s, ¬L)`).
Source: [[corr-wf14b-inventory]] 061 / landscape-final.md S5
Kind: D
Fidelity: exact (product form) -/
def cost (μ : Distr (S × Bool)) (c h k : ℝ) (b : Bool) (s : S) : ℝ :=
  if b then legMass μ s * h + sigMass μ s * k else nonlegMass μ s * c

/-- **S5: the loss functional** `ℓ*(r) = ∑_s P*(s)[π*(s) r(s) h + (1 − π*(s))(1 − r(s)) c + r(s) k]`
in product form: `∑_s cost(r s, s)`.
Source: [[corr-wf14b-inventory]] 061 / landscape-final.md S5
Kind: D
Fidelity: exact (product form) -/
def loss (μ : Distr (S × Bool)) (r : S → Bool) (c h k : ℝ) : ℝ := ∑ s, cost μ c h k (r s) s

/-- The pushers' outcome `P*(lands) = 1 − ∑_s P*(s) r(s)` (S5).
Source: [[corr-wf14b-inventory]] 061 / landscape-final.md S5 ("the pushers' outcome")
Kind: D
Fidelity: exact -/
def landsMass (μ : Distr (S × Bool)) (r : S → Bool) : ℝ := ∑ s, sigMass μ s * (1 - rI r s)

/-- **D6, absolute**: never resist (`r ≡ 0`).
Source: [[corr-wf14b-inventory]] 061 / landscape-final.md D6, R4
Kind: D
Fidelity: exact -/
def absoluteRule : S → Bool := fun _ => false

/-- **D6, none**: always resist (`r ≡ 1`).
Source: [[corr-wf14b-inventory]] 061 / landscape-final.md D6, R4
Kind: D
Fidelity: exact -/
def noneRule : S → Bool := fun _ => true

/-- **The objective Bayes rule** `r*(s) = 1[π*(s) < q_k]` in product form: resist iff
`μ(s, L) < q_k · P*(s)`. At `P*(s) = 0` both sides are `0` and the rule accepts (the decision there
costs nothing either way).
Source: [[corr-wf14b-inventory]] 061 / landscape-final.md S5 ("Objective Bayes rule")
Kind: D
Fidelity: exact (product form; ties at `π* = q_k` accept, as the source's strict `<`) -/
noncomputable def bayesRule (μ : Distr (S × Bool)) (c h k : ℝ) : S → Bool :=
  fun s => decide (legMass μ s < qk c h k * sigMass μ s)

/-- **D6, conditioned**: the agent's rule from its credence `π̂` and priced erosion `k̂`: resist iff
`π̂(s) < q_k̂`.
Source: [[corr-wf14b-inventory]] 061 / landscape-final.md D6, R4
Kind: D
Fidelity: exact -/
noncomputable def conditionedRule (πh : S → ℝ) (kh c h : ℝ) : S → Bool :=
  fun s => decide (πh s < qk c h kh)

/-- **D4: legitimacy coverage at tolerance `δ`**: `|π̂(s) − π*(s)| ≤ δ` on every positive-mass signal.
Source: [[corr-wf14b-inventory]] 061 / landscape-final.md D4
Kind: D
Fidelity: exact -/
def covered (πh : S → ℝ) (μ : Distr (S × Bool)) (δ : ℝ) : Prop :=
  ∀ s, 0 < sigMass μ s → |πh s - piStar μ s| ≤ δ

/-- **D6′: the anticipatory erosion inequality** — the conditioned agent resists ahead of time iff
`p_push [(1 − π̂) c − π̂ h] > k̂`.
Source: [[corr-wf14b-inventory]] 061, 065 / landscape-final.md D6′, P5
Kind: D
Fidelity: exact -/
def erodes (ppush πh c h kh : ℝ) : Prop := ppush * ((1 - πh) * c - πh * h) > kh

/-- **D5: the erosion stock** `k̂ = ∑_j p_j (ℓ̂_j(none) − ℓ̂_j(cond))` over a finite index of future
classes, from given per-class losses.
Source: [[corr-wf14b-inventory]] 061, 065 / landscape-final.md D5, P5
Kind: D
Fidelity: exact -/
def stock {n : ℕ} (p lnone lcond : Fin n → ℝ) : ℝ := ∑ j, p j * (lnone j - lcond j)

/-! ## Basic facts about the masses -/

/-- `legMass_nonneg` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma legMass_nonneg (μ : Distr (S × Bool)) (s : S) : 0 ≤ legMass μ s := μ.nonneg _

/-- `nonlegMass_nonneg` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma nonlegMass_nonneg (μ : Distr (S × Bool)) (s : S) : 0 ≤ nonlegMass μ s := μ.nonneg _

/-- `sigMass_nonneg` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sigMass_nonneg (μ : Distr (S × Bool)) (s : S) : 0 ≤ sigMass μ s :=
  add_nonneg (legMass_nonneg μ s) (nonlegMass_nonneg μ s)

/-- `legMass_le_sigMass` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma legMass_le_sigMass (μ : Distr (S × Bool)) (s : S) : legMass μ s ≤ sigMass μ s := by
  unfold sigMass; linarith [nonlegMass_nonneg μ s]

/-- The signal masses sum to one. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_sigMass (μ : Distr (S × Bool)) : ∑ s, sigMass μ s = 1 := by
  have h := μ.sum_eq_one
  rw [Fintype.sum_prod_type] at h
  simp only [Fintype.sum_bool] at h
  simpa [sigMass, legMass, nonlegMass, sum_add_distrib, add_comm] using h

/-- `∑ nonlegMass = 1 − λ`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_nonlegMass (μ : Distr (S × Bool)) : ∑ s, nonlegMass μ s = 1 - lam μ := by
  have h := sum_sigMass μ
  simp only [sigMass, sum_add_distrib] at h
  unfold lam; linarith

/-- `lam_nonneg` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma lam_nonneg (μ : Distr (S × Bool)) : 0 ≤ lam μ := sum_nonneg fun s _ => legMass_nonneg μ s

/-- `lam_le_one` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma lam_le_one (μ : Distr (S × Bool)) : lam μ ≤ 1 := by
  have := sum_nonlegMass μ
  have := sum_nonneg fun s (_ : s ∈ univ) => nonlegMass_nonneg μ s
  linarith

/-- `sigMass_eq_zero` (supporting lemma): zero signal mass forces both masses to zero.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sigMass_eq_zero {μ : Distr (S × Bool)} {s : S} (h : sigMass μ s = 0) :
    legMass μ s = 0 ∧ nonlegMass μ s = 0 := by
  unfold sigMass at h
  constructor <;> linarith [legMass_nonneg μ s, nonlegMass_nonneg μ s]

/-- **The key algebra** `(1 − π)c − πh − k = (c + h)(q_k − π)` in product form: the resist-minus-accept
cost at a signal is `(c + h)(μ(s, L) − q_k P*(s))`.
Source: [[corr-wf14b-inventory]] 063 / landscape-final.md P3 ("using `(1−π)c − πh − k = (c+h)(q_k − π)`")
Kind: L
Fidelity: exact -/
lemma cost_true_sub_false (μ : Distr (S × Bool)) {c h : ℝ} (k : ℝ) (hch : 0 < c + h) (s : S) :
    cost μ c h k true s - cost μ c h k false s = (c + h) * (legMass μ s - qk c h k * sigMass μ s) := by
  simp only [cost, Bool.false_eq_true, ↓reduceIte, qk, sigMass]
  field_simp
  ring

/-! ## Statement 1: the unconditional rows are priced by `λ` alone (P1) -/

/-- **Statement 1(a)**: `ℓ*(absolute) = (1 − λ) c` for every signal structure.
Source: [[corr-wf14b-inventory]] 062 / landscape-final.md Statement 1, P1
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem loss_absolute (μ : Distr (S × Bool)) (c h k : ℝ) :
    loss μ absoluteRule c h k = (1 - lam μ) * c := by
  simp only [loss, cost, absoluteRule, Bool.false_eq_true, ↓reduceIte, ← sum_mul, sum_nonlegMass]

/-- **Statement 1(b)**: `ℓ*(none) = λ h + k` for every signal structure.
Source: [[corr-wf14b-inventory]] 062 / landscape-final.md Statement 1, P1
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem loss_none (μ : Distr (S × Bool)) (c h k : ℝ) :
    loss μ noneRule c h k = lam μ * h + k := by
  simp only [loss, cost, noneRule, ↓reduceIte, sum_add_distrib, ← sum_mul, sum_sigMass, one_mul]
  rfl

/-- **Statement 1(c)**: absolute is strictly better than none iff `λ > q_k` (both directions).
Source: [[corr-wf14b-inventory]] 062 / landscape-final.md Statement 1, P1
Kind: L
Fidelity: exact
Hyps: (a) `0 < c + h` is where `q_k` is defined -/
theorem absolute_lt_none_iff (μ : Distr (S × Bool)) {c h : ℝ} (k : ℝ) (hch : 0 < c + h) :
    loss μ absoluteRule c h k < loss μ noneRule c h k ↔ qk c h k < lam μ := by
  rw [loss_absolute, loss_none, qk, div_lt_iff₀ hch]
  constructor <;> intro H <;> nlinarith

/-- The absolute row lets every push land: `P*(lands) = 1` for every law.
Source: [[corr-wf14b-2-inventory]] 2-006 / thornley-respondent.md P12 (the accept-side pair)
Kind: L
Fidelity: exact -/
theorem landsMass_absolute (μ : Distr (S × Bool)) : landsMass μ absoluteRule = 1 := by
  simp [landsMass, rI, absoluteRule, sum_sigMass]

/-! ## Statement 2: the Bayes rule is the pointwise minimizer (P2) -/

/-- **The pointwise minimization**: at every signal the Bayes decision costs no more than either
decision (the tie `μ(s, L) = q_k P*(s)` accepts at equal cost).
Source: [[corr-wf14b-inventory]] 062 / landscape-final.md P2 ("the global minimizer is pointwise")
Kind: L
Fidelity: exact -/
lemma cost_bayes_le (μ : Distr (S × Bool)) {c h : ℝ} (k : ℝ) (hch : 0 < c + h) (s : S) (b : Bool) :
    cost μ c h k (bayesRule μ c h k s) s ≤ cost μ c h k b s := by
  have key := cost_true_sub_false μ k hch s
  by_cases hs : legMass μ s < qk c h k * sigMass μ s
  · have hb : bayesRule μ c h k s = true := by simp [bayesRule, hs]
    rw [hb]
    cases b
    · nlinarith
    · exact le_rfl
  · have hb : bayesRule μ c h k s = false := by simp [bayesRule, hs]
    rw [hb]
    cases b
    · exact le_rfl
    · rw [not_lt] at hs; nlinarith

/-- **Statement 2 (weak domination)**: `ℓ*(r*) ≤ ℓ*(r)` for every rule `r`, in particular both constants.
Source: [[corr-wf14b-inventory]] 062 / landscape-final.md Statement 2, P2
Kind: L
Fidelity: exact
Hyps: (a) `0 < c + h` -/
theorem loss_bayes_le (μ : Distr (S × Bool)) {c h : ℝ} (k : ℝ) (hch : 0 < c + h) (r : S → Bool) :
    loss μ (bayesRule μ c h k) c h k ≤ loss μ r c h k :=
  sum_le_sum fun s _ => cost_bayes_le μ k hch s (r s)

/-- **Statement 2, strict against absolute**: if some signal has `μ(s, L) < q_k P*(s)` (strictly below
the threshold, which forces `P*(s) > 0`) the Bayes rule beats absolute acceptance strictly.
Source: [[corr-wf14b-inventory]] 062 / landscape-final.md Statement 2 ("strictly whenever two
positive-probability signals straddle `q_k`") — the absolute half
Kind: L
Fidelity: exact (the strictness hypothesis stated exactly; a tie gives equality)
Hyps: (a) only -/
theorem loss_bayes_lt_absolute (μ : Distr (S × Bool)) {c h : ℝ} (k : ℝ) (hch : 0 < c + h)
    (hs : ∃ s, legMass μ s < qk c h k * sigMass μ s) :
    loss μ (bayesRule μ c h k) c h k < loss μ absoluteRule c h k := by
  obtain ⟨s₀, hs₀⟩ := hs
  unfold loss
  apply sum_lt_sum (fun s _ => cost_bayes_le μ k hch s _) ⟨s₀, mem_univ _, ?_⟩
  have key := cost_true_sub_false μ k hch s₀
  have hb : bayesRule μ c h k s₀ = true := by simp [bayesRule, hs₀]
  rw [hb]
  show cost μ c h k true s₀ < cost μ c h k false s₀
  nlinarith

/-- **Statement 2, strict against none**: if some signal has `μ(s, L) > q_k P*(s)` the Bayes rule beats
always-resist strictly.
Source: [[corr-wf14b-inventory]] 062 / landscape-final.md Statement 2 — the none half
Kind: L
Fidelity: exact (strictness hypothesis stated exactly)
Hyps: (a) only -/
theorem loss_bayes_lt_none (μ : Distr (S × Bool)) {c h : ℝ} (k : ℝ) (hch : 0 < c + h)
    (hs : ∃ s, qk c h k * sigMass μ s < legMass μ s) :
    loss μ (bayesRule μ c h k) c h k < loss μ noneRule c h k := by
  obtain ⟨s₀, hs₀⟩ := hs
  unfold loss
  apply sum_lt_sum (fun s _ => cost_bayes_le μ k hch s _) ⟨s₀, mem_univ _, ?_⟩
  have key := cost_true_sub_false μ k hch s₀
  have hb : bayesRule μ c h k s₀ = false := by simp [bayesRule, not_lt.2 hs₀.le]
  rw [hb]
  show cost μ c h k false s₀ < cost μ c h k true s₀
  nlinarith

/-- **Statement 2, strict against both** when positive-mass signals straddle `q_k` (one strictly
below, one strictly above).
Source: [[corr-wf14b-inventory]] 062 / landscape-final.md Statement 2
Kind: C (the two halves)
Fidelity: exact
Hyps: (a) only -/
theorem loss_bayes_lt_both (μ : Distr (S × Bool)) {c h : ℝ} (k : ℝ) (hch : 0 < c + h)
    (hlo : ∃ s, legMass μ s < qk c h k * sigMass μ s)
    (hhi : ∃ s, qk c h k * sigMass μ s < legMass μ s) :
    loss μ (bayesRule μ c h k) c h k < loss μ absoluteRule c h k ∧
      loss μ (bayesRule μ c h k) c h k < loss μ noneRule c h k :=
  ⟨loss_bayes_lt_absolute μ k hch hlo, loss_bayes_lt_none μ k hch hhi⟩

/-! ## The conditioned rule at `δ = 0`, `k̂ = k` is the Bayes rule (Statement 2's identification) -/

/-- On a positive-mass signal where the credence is exact, the conditioned rule at `k̂ = k` is the
Bayes rule.
Source: [[corr-wf14b-inventory]] 062 / landscape-final.md Statement 2 ("at `δ = 0` and `k̂ = k` the
conditioned rule is the pointwise minimizer")
Kind: L
Fidelity: exact (on the support; off it both decisions cost `0`) -/
lemma conditionedRule_eq_bayes_of_exact (μ : Distr (S × Bool)) (πh : S → ℝ) (c h k : ℝ) (s : S)
    (hpos : 0 < sigMass μ s) (hex : πh s = piStar μ s) :
    conditionedRule πh k c h s = bayesRule μ c h k s := by
  have key : πh s < qk c h k ↔ legMass μ s < qk c h k * sigMass μ s := by
    rw [hex, piStar, div_lt_iff₀ hpos, mul_comm]
  by_cases hp : legMass μ s < qk c h k * sigMass μ s
  · simp [conditionedRule, bayesRule, hp, key.2 hp]
  · simp [conditionedRule, bayesRule, hp, mt key.1 hp]

/-- Zero-mass signals cost nothing under any decision.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cost_eq_zero_of_sigMass_eq_zero (μ : Distr (S × Bool)) (c h k : ℝ) (b : Bool) {s : S}
    (hs : sigMass μ s = 0) : cost μ c h k b s = 0 := by
  obtain ⟨h1, h2⟩ := sigMass_eq_zero hs
  cases b <;> simp [cost, h1, h2, hs]

/-- **Statement 2, the identification**: covered at `δ = 0` with `k̂ = k`, the conditioned rule has the
Bayes loss (the rules agree on the support, and off it nothing costs).
Source: [[corr-wf14b-inventory]] 062 / landscape-final.md Statement 2; S6 ("at `δ = 0, k̂ = k` the
conditioned rule *is* the Bayes rule")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem loss_conditioned_eq_bayes_of_covered_zero (μ : Distr (S × Bool)) (πh : S → ℝ) (c h k : ℝ)
    (hcov : covered πh μ 0) :
    loss μ (conditionedRule πh k c h) c h k = loss μ (bayesRule μ c h k) c h k := by
  unfold loss
  refine sum_congr rfl fun s _ => ?_
  rcases (sigMass_nonneg μ s).lt_or_eq with hpos | hzero
  · rw [conditionedRule_eq_bayes_of_exact μ πh c h k s hpos]
    have := hcov s hpos
    rw [abs_nonpos_iff] at this
    linarith
  · rw [cost_eq_zero_of_sigMass_eq_zero μ c h k _ hzero.symm,
      cost_eq_zero_of_sigMass_eq_zero μ c h k _ hzero.symm]

/-! ## The erosion inequality is antitone in the priced stock (Statement 5(c), P5, C6) -/

/-- **D6′'s resist set is non-increasing in `k̂`**: eroding at a larger priced stock implies eroding at a
smaller one.
Source: [[corr-wf14b-inventory]] 065 / landscape-final.md Statement 5(c), P5 ("the resist set is
non-increasing in `k̂`")
Kind: L
Fidelity: exact -/
theorem erodes_antitone {ppush πh c h kh kh' : ℝ} (hk : kh ≤ kh') (he : erodes ppush πh c h kh') :
    erodes ppush πh c h kh := by
  unfold erodes at *; linarith

/-- The push-time rule is the `p_push = 1` slice of D6′.
Source: [[corr-wf14b-inventory]] 065 / landscape-final.md D6′ ("the push-time inequality is the
`p_push = 1` slice")
Kind: L
Fidelity: exact -/
theorem erodes_one_iff (πh c h kh : ℝ) : erodes 1 πh c h kh ↔ (1 - πh) * c - πh * h > kh := by
  unfold erodes; rw [one_mul]

end Map

end Cleanroom.Corrigibility.CorrLandscape
