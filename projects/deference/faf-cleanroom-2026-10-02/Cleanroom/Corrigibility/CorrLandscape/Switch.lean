import Cleanroom.Corrigibility.CorrLandscape.Trichotomy

/-!
# `corr-landscape` — `Switch`: the switch rule and the max-safe-`δ` closed form (T17)

Hudson-voice item 2 / `switch_rule.py` ([[corr-wf14b-2-inventory]] 2-005): the conditioned rule scored
at its **worst case** over the coverage band `[π*(s) − δ, π*(s) + δ]` (the adversary picks the decision
wherever the band straddles `q = c/(c+h)`; `k = 0`, the cognition column):
`can_accept ↔ π* + δ ≥ q`, `can_resist ↔ π* − δ < q`, `worst = ∑_s P*(s) · max{admissible costs}`
(`worstAt`, `worst`, in product form).

* (a) **Structural lemma** (hudson-respondent C2): if `π*(s) ≥ q` on every positive-mass signal the Bayes
  rule is absolute (`bayes_eq_absolute_of_all_ge`) and `worst ≥ ℓ*(absolute)` for every `δ ≥ 0`
  (`worst_ge_absolute`); and in general `worst ≤ ℓ*(Bayes) + (c+h)δ` (`worst_le_bayes_add`): the legitimacy
  model is a pure liability, bounded by Proposition R′'s `(c+h)δ`.
* (b) **The exact two-signal rule** (`two_signal_rule`): with `π*(0) < q ≤ π*(1)` and positive masses, the
  conditioned row beats absolute in the worst case iff `δ < q − π*(0)` **and** (`δ ≤ π*(1) − q` or
  `λ < q`). The mandate's "iff `δ < q − π*(0)`" (its own derivation, marked "verify, do not take") omits the
  second clause: when the band also straddles `s = 1` the worst case is the *none* row, which beats
  absolute only if `λ < q` — `mandate_rule_refuted` is the counterexample (`λ = 23/50 ≥ q = 9/20`, `δ = 1/10
  < 3/20 = q − π*(0)`, worst `253/50 > 243/50 = ℓ*(absolute)`). Under the side condition
  `q − π*(0) ≤ π*(1) − q ∨ λ < q` the closed form `maxSafeDelta = q − π*(0)` is exact
  (`two_signal_closed_form`), a **supremum not attained** (at `δ = maxSafeDelta` the worst case *is* the
  absolute row). The side condition holds in every tabulated cell: pause stakes `77/410, 17/110, 1/10`
  at `λ = 1/10, 3/10, 1/2` and none at `7/10, 9/10`; `c = h = 1`: `20/41, 5/11, 2/5, 5/17`, none at `9/10`;
  whole-line `(9/10, 11/10)`: `359/820, 89/220, 7/20, 83/340`, none at `9/10`.
* **Finding**: the voice's tabulated `0.1875, 0.1525, 0.0975, …` are the `1/400`-grid values just below
  these exact bounds (`grid_values`); presentation, not error.
-/

namespace Cleanroom.Corrigibility.CorrLandscape

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect
open Classical

set_option linter.unusedSectionVars false

namespace Switch

open Map Trichotomy

variable {S : Type} [Fintype S] [DecidableEq S]

/-- `can_accept`: the band reaches `q` from below, `π* + δ ≥ q` (product form).
Source: [[corr-wf14b-2-inventory]] 2-005 / `switch_rule.py` (`can_accept = hi >= q`)
Kind: D
Fidelity: exact (product form) -/
def canAccept (μ : Distr (S × Bool)) (c h δ : ℝ) (s : S) : Prop :=
  qk c h 0 * sigMass μ s ≤ legMass μ s + δ * sigMass μ s

/-- `can_resist`: the band reaches below `q`, `π* − δ < q` (product form).
Source: [[corr-wf14b-2-inventory]] 2-005 / `switch_rule.py` (`can_resist = lo < q`)
Kind: D
Fidelity: exact (product form) -/
def canResist (μ : Distr (S × Bool)) (c h δ : ℝ) (s : S) : Prop :=
  legMass μ s - δ * sigMass μ s < qk c h 0 * sigMass μ s

/-- **The worst-case per-signal cost** over the band: the adversary's decision among the admissible ones.
Source: [[corr-wf14b-2-inventory]] 2-005 / `switch_rule.py` (`w = max(acc if can_accept else 0, res if
can_resist else 0)`)
Kind: D
Fidelity: exact (the script's `0` placeholders never win since one of the two is always admissible for
`δ ≥ 0`, `canAccept_or_canResist`; the final `else` branch, the resist cost when neither is admissible,
is reachable only for `δ < 0`, and every headline carries `0 ≤ δ` — audit r1, N13) -/
noncomputable def worstAt (μ : Distr (S × Bool)) (c h δ : ℝ) (s : S) : ℝ :=
  if canAccept μ c h δ s ∧ canResist μ c h δ s then max (nonlegMass μ s * c) (legMass μ s * h)
  else if canAccept μ c h δ s then nonlegMass μ s * c else legMass μ s * h

/-- **The worst-case loss** of the conditioned rule over the coverage band.
Source: [[corr-wf14b-2-inventory]] 2-005 / `switch_rule.py` (`worst`)
Kind: D
Fidelity: exact -/
noncomputable def worst (μ : Distr (S × Bool)) (c h δ : ℝ) : ℝ := ∑ s, worstAt μ c h δ s

/-- One of the two decisions is always admissible for `δ ≥ 0`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma canAccept_or_canResist (μ : Distr (S × Bool)) (c h δ : ℝ) (hδ : 0 ≤ δ) (s : S) :
    canAccept μ c h δ s ∨ canResist μ c h δ s := by
  by_cases hA : canAccept μ c h δ s
  · exact Or.inl hA
  · right
    unfold canAccept at hA; unfold canResist
    rw [not_le] at hA
    nlinarith [mul_nonneg hδ (sigMass_nonneg μ s)]

/-- `worstAt_ge_accept` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma worstAt_ge_accept (μ : Distr (S × Bool)) (c h δ : ℝ) (s : S) (hA : canAccept μ c h δ s) :
    nonlegMass μ s * c ≤ worstAt μ c h δ s := by
  unfold worstAt
  by_cases hR : canResist μ c h δ s
  · simp [hA, hR]
  · simp [hA, hR]

/-- `worstAt_ge_resist` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma worstAt_ge_resist (μ : Distr (S × Bool)) (c h δ : ℝ) (s : S) (hR : canResist μ c h δ s) :
    legMass μ s * h ≤ worstAt μ c h δ s := by
  unfold worstAt
  by_cases hA : canAccept μ c h δ s
  · simp [hA, hR]
  · simp [hA, hR]

/-! ## (a) the structural lemma -/

/-- **On a class where every positive-mass posterior is `≥ q`, the Bayes rule is absolute.**
Source: [[corr-wf14b-2-inventory]] 2-005 / hudson-respondent.md C2 ("when both posteriors exceed `q`, the
Bayes rule *is* `σ^acc`")
Kind: L
Fidelity: exact -/
theorem bayes_eq_absolute_of_all_ge (μ : Distr (S × Bool)) (c h : ℝ)
    (hall : ∀ s, 0 < sigMass μ s → qk c h 0 * sigMass μ s ≤ legMass μ s) :
    bayesRule μ c h 0 = absoluteRule := by
  funext s
  rcases (sigMass_nonneg μ s).lt_or_eq with hpos | hzero
  · simp [bayesRule, absoluteRule, not_lt.2 (hall s hpos)]
  · obtain ⟨h1, -⟩ := sigMass_eq_zero hzero.symm
    simp [bayesRule, absoluteRule, h1, ← hzero]

/-- **The legitimacy model is a pure liability on a well-run class**: with every positive-mass posterior
`≥ q`, `ℓ*(absolute) ≤ worst μ δ` for every `δ ≥ 0`.
Source: [[corr-wf14b-2-inventory]] 2-005 / hudson-respondent.md C2 ("a miscalibration can only flip a
decision away from it")
Kind: P (small)
Fidelity: exact
Hyps: (a) only -/
theorem worst_ge_absolute (μ : Distr (S × Bool)) (c h δ : ℝ) (hδ : 0 ≤ δ)
    (hall : ∀ s, 0 < sigMass μ s → qk c h 0 * sigMass μ s ≤ legMass μ s) :
    loss μ absoluteRule c h 0 ≤ worst μ c h δ := by
  unfold loss worst
  refine sum_le_sum fun s _ => ?_
  have hA : canAccept μ c h δ s := by
    unfold canAccept
    rcases (sigMass_nonneg μ s).lt_or_eq with hpos | hzero
    · nlinarith [hall s hpos, mul_nonneg hδ (sigMass_nonneg μ s)]
    · obtain ⟨h1, -⟩ := sigMass_eq_zero hzero.symm
      rw [← hzero, h1]; simp
  simpa [cost, absoluteRule] using worstAt_ge_accept μ c h δ s hA

/-- **The worst case is within `(c+h)δ` of the Bayes loss**: `worst μ δ ≤ ℓ*(Bayes) + (c+h)δ`
(Proposition R′'s constant, for the adversarial scoring).
Source: [[corr-wf14b-2-inventory]] 2-005 / hudson-respondent.md C2 ("bounded by Proposition R′'s
`(c+h)δ`")
Kind: P
Fidelity: exact
Hyps: (a) `0 < c + h`, `0 ≤ δ` -/
theorem worst_le_bayes_add (μ : Distr (S × Bool)) {c h : ℝ} (δ : ℝ) (hch : 0 < c + h) (hδ : 0 ≤ δ) :
    worst μ c h δ ≤ loss μ (bayesRule μ c h 0) c h 0 + (c + h) * δ := by
  unfold worst loss
  have hpt : ∀ s, worstAt μ c h δ s ≤ cost μ c h 0 (bayesRule μ c h 0 s) s + sigMass μ s * ((c + h) * δ) := by
    intro s
    have key := cost_true_sub_false μ 0 hch s
    have hsig := sigMass_nonneg μ s
    have hnn : 0 ≤ sigMass μ s * ((c + h) * δ) := mul_nonneg hsig (mul_nonneg hch.le hδ)
    have ct : cost μ c h 0 true s = legMass μ s * h := by simp [cost]
    have cf : cost μ c h 0 false s = nonlegMass μ s * c := by simp [cost]
    unfold worstAt
    by_cases hA : canAccept μ c h δ s <;> by_cases hR : canResist μ c h δ s
    · -- straddled: `|acc − res| ≤ (c+h) δ P*(s)`
      simp only [hA, hR, and_self, if_true]
      unfold canAccept at hA; unfold canResist at hR
      by_cases hb : legMass μ s < qk c h 0 * sigMass μ s
      · have hb' : bayesRule μ c h 0 s = true := by simp [bayesRule, hb]
        rw [hb', ct, max_le_iff]
        constructor <;> nlinarith
      · have hb' : bayesRule μ c h 0 s = false := by simp [bayesRule, hb]
        rw [hb', cf, max_le_iff]
        rw [not_lt] at hb
        constructor <;> nlinarith
    · simp only [hA, hR, and_false, if_false, if_true]
      unfold canAccept at hA; unfold canResist at hR
      rw [not_lt] at hR
      have hb : ¬ legMass μ s < qk c h 0 * sigMass μ s := by
        rw [not_lt]; nlinarith [mul_nonneg hδ hsig]
      have hb' : bayesRule μ c h 0 s = false := by simp [bayesRule, hb]
      rw [hb', cf]; linarith
    · simp only [hA, hR, false_and, if_false]
      unfold canAccept at hA; unfold canResist at hR
      rw [not_le] at hA
      have hb : legMass μ s < qk c h 0 * sigMass μ s := by nlinarith [mul_nonneg hδ hsig]
      have hb' : bayesRule μ c h 0 s = true := by simp [bayesRule, hb]
      rw [hb', ct]; linarith
    · exact absurd (canAccept_or_canResist μ c h δ hδ s) (by tauto)
  calc ∑ s, worstAt μ c h δ s ≤ ∑ s, (cost μ c h 0 (bayesRule μ c h 0 s) s + sigMass μ s * ((c + h) * δ)) :=
        sum_le_sum fun s _ => hpt s
    _ = ∑ s, cost μ c h 0 (bayesRule μ c h 0 s) s + (c + h) * δ := by
        rw [sum_add_distrib, ← sum_mul, sum_sigMass, one_mul]

/-! ## (b) the exact two-signal rule -/

/-- **The exact two-signal rule.** With positive masses and `π*(0) < q ≤ π*(1)`, the conditioned row
beats absolute in the worst case iff `δ < q − π*(0)` **and** (`δ ≤ π*(1) − q` **or** `λ < q`), all in
product form. The second clause is the mandate's missing case: once the band straddles `s = 1` too, the
worst case is the *none* row, which beats absolute iff `λ < q` (Statement 1).
Source: [[corr-wf14b-2-inventory]] 2-005 / hudson-voice.md item 2; mandate T17(b) ("verify, do not take")
Kind: P
Fidelity: stronger: the mandate's rule with its missing clause supplied
Hyps: (a) `0 < c + h`, `0 ≤ δ` -/
theorem two_signal_rule (μ : Distr (Bool × Bool)) {c h : ℝ} (δ : ℝ) (hch : 0 < c + h) (hδ : 0 ≤ δ)
    (hp0 : 0 < sigMass μ false) (hp1 : 0 < sigMass μ true)
    (h0 : legMass μ false < qk c h 0 * sigMass μ false) (h1 : qk c h 0 * sigMass μ true ≤ legMass μ true) :
    worst μ c h δ < loss μ absoluteRule c h 0 ↔
      legMass μ false + δ * sigMass μ false < qk c h 0 * sigMass μ false ∧
        (qk c h 0 * sigMass μ true ≤ legMass μ true - δ * sigMass μ true ∨ lam μ < qk c h 0) := by
  have k0 := cost_true_sub_false μ 0 hch false
  have k1 := cost_true_sub_false μ 0 hch true
  simp only [cost, Bool.false_eq_true, ↓reduceIte, add_zero, mul_zero] at k0 k1
  have hR0 : canResist μ c h δ false := by
    unfold canResist; nlinarith [mul_nonneg hδ hp0.le]
  have hA1 : canAccept μ c h δ true := by
    unfold canAccept; nlinarith [mul_nonneg hδ hp1.le]
  have hres0 : legMass μ false * h < nonlegMass μ false * c := by nlinarith [mul_pos hch (sub_pos.2 h0)]
  have hres1 : nonlegMass μ true * c ≤ legMass μ true * h := by nlinarith [mul_nonneg hch.le (sub_nonneg.2 h1)]
  have hsum : sigMass μ false + sigMass μ true = 1 := by
    have := sum_sigMass μ; simpa [Fintype.sum_bool, add_comm] using this
  have hlam : lam μ = legMass μ false + legMass μ true := by simp [lam, Fintype.sum_bool, add_comm]
  have habs : loss μ absoluteRule c h 0 = nonlegMass μ false * c + nonlegMass μ true * c := by
    simp [loss, Fintype.sum_bool, cost, absoluteRule, add_comm]
  have hw0 : worstAt μ c h δ false = if canAccept μ c h δ false then nonlegMass μ false * c else legMass μ false * h := by
    unfold worstAt
    by_cases hA : canAccept μ c h δ false
    · simp [hA, hR0, max_eq_left hres0.le]
    · simp [hA]
  have hw1 : worstAt μ c h δ true = if canResist μ c h δ true then legMass μ true * h else nonlegMass μ true * c := by
    unfold worstAt
    by_cases hR : canResist μ c h δ true
    · simp [hA1, hR, max_eq_right hres1]
    · simp [hA1, hR]
  have hworst : worst μ c h δ = worstAt μ c h δ false + worstAt μ c h δ true := by
    simp [worst, Fintype.sum_bool, add_comm]
  rw [hworst, hw0, hw1, habs]
  have eA : (legMass μ false + δ * sigMass μ false < qk c h 0 * sigMass μ false) ↔ ¬ canAccept μ c h δ false := by
    unfold canAccept; rw [not_le]
  have eR : (qk c h 0 * sigMass μ true ≤ legMass μ true - δ * sigMass μ true) ↔ ¬ canResist μ c h δ true := by
    unfold canResist; rw [not_lt]
  rw [eA, eR]
  by_cases hA : canAccept μ c h δ false <;> by_cases hR : canResist μ c h δ true <;>
    simp only [hA, hR, if_true, if_false, not_true_eq_false, not_false_eq_true, true_or, false_or,
      false_and, true_and, iff_false, iff_true, not_lt]
  · linarith
  · linarith
  · -- straddled on both sides: the worst case is the `none` row; it beats absolute iff `λ < q`
    rw [hlam]
    have hq : (c + h) * (qk c h 0 * sigMass μ false) + (c + h) * (qk c h 0 * sigMass μ true) =
        (c + h) * qk c h 0 := by
      rw [← mul_add, ← mul_add, hsum, mul_one]
    constructor
    · intro H
      have : (c + h) * (legMass μ false + legMass μ true - qk c h 0) < 0 := by linarith
      by_contra hcon
      rw [not_lt] at hcon
      have := mul_nonneg hch.le (sub_nonneg.2 hcon)
      linarith
    · intro H
      have : (c + h) * (legMass μ false + legMass μ true - qk c h 0) < 0 :=
        mul_neg_of_pos_of_neg hch (by linarith)
      linarith
  · linarith

/-- **The max-safe `δ` closed form** `q − π*(0)` (a named real; the headline guards it by the two-signal
hypotheses).
Source: [[corr-wf14b-2-inventory]] 2-005 (difficulty line: "to state the max-safe-`δ` as a closed form");
mandate T17(b)
Kind: D
Fidelity: exact under the two-signal hypotheses and the side condition -/
noncomputable def maxSafeDelta (μ : Distr (Bool × Bool)) (c h : ℝ) : ℝ := qk c h 0 - piStar μ false

/-- **The closed form is exact under the side condition** `q − π*(0) ≤ π*(1) − q ∨ λ < q`: for every
`δ ≥ 0`, the conditioned row beats absolute in the worst case iff `δ < maxSafeDelta`. The supremum is not
attained: at `δ = maxSafeDelta` flipping `s = 0` to accept *is* the absolute rule.
Source: [[corr-wf14b-2-inventory]] 2-005 / hudson-voice.md item 2; mandate T17(b)
Kind: P
Fidelity: exact (with the side condition the mandate's derivation lacked)
Hyps: (a) only -/
theorem two_signal_closed_form (μ : Distr (Bool × Bool)) {c h : ℝ} (hch : 0 < c + h)
    (hp0 : 0 < sigMass μ false) (hp1 : 0 < sigMass μ true)
    (h0 : legMass μ false < qk c h 0 * sigMass μ false) (h1 : qk c h 0 * sigMass μ true ≤ legMass μ true)
    (hside : maxSafeDelta μ c h ≤ piStar μ true - qk c h 0 ∨ lam μ < qk c h 0) :
    ∀ δ, 0 ≤ δ → (worst μ c h δ < loss μ absoluteRule c h 0 ↔ δ < maxSafeDelta μ c h) := by
  intro δ hδ
  rw [two_signal_rule μ δ hch hδ hp0 hp1 h0 h1]
  have e0 : (legMass μ false + δ * sigMass μ false < qk c h 0 * sigMass μ false) ↔ δ < maxSafeDelta μ c h := by
    unfold maxSafeDelta piStar
    rw [lt_sub_iff_add_lt]
    have : δ + legMass μ false / sigMass μ false = (δ * sigMass μ false + legMass μ false) / sigMass μ false := by
      field_simp
    rw [this, div_lt_iff₀ hp0]
    constructor <;> intro H <;> linarith
  have e1 : (qk c h 0 * sigMass μ true ≤ legMass μ true - δ * sigMass μ true) ↔ δ ≤ piStar μ true - qk c h 0 := by
    unfold piStar
    constructor
    · intro H
      rw [le_sub_iff_add_le, le_div_iff₀ hp1]; linarith
    · intro H
      rw [le_sub_iff_add_le, le_div_iff₀ hp1] at H; linarith
  rw [e0, e1]
  constructor
  · exact fun H => H.1
  · intro H
    refine ⟨H, ?_⟩
    rcases hside with hs | hs
    · left; linarith
    · right; exact hs

/-! ## The counterexample to the mandate's unconditional rule -/

/-- A two-signal law with `p_0 = 1/5`, `p_1 = 4/5`, `π*(0) = 3/10`, `π*(1) = 1/2`: `λ = 23/50`.
Source: mandate T17(b) (the mandate writer's rule, checked)
Kind: D
Fidelity: n/a (witness) -/
noncomputable def cxLaw : Distr (Bool × Bool) where
  mass p := match p with
    | (true, true) => 2 / 5
    | (false, true) => 3 / 50
    | (true, false) => 2 / 5
    | (false, false) => 7 / 50
  nonneg p := by rcases p with ⟨s, l⟩; cases s <;> cases l <;> simp <;> norm_num
  sum_eq_one := by rw [Fintype.sum_prod_type]; simp [Fintype.sum_bool]; norm_num

/-- `cxLaw` masses. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cxLaw_mass : legMass cxLaw true = 2 / 5 ∧ legMass cxLaw false = 3 / 50 ∧
    nonlegMass cxLaw true = 2 / 5 ∧ nonlegMass cxLaw false = 7 / 50 := by
  simp [cxLaw, legMass, nonlegMass]

/-- **The mandate's "iff `δ < q − π*(0)`" refuted**: at stakes `c = 9`, `h = 11` (`q = 9/20`), `δ = 1/10`
is below `q − π*(0) = 3/20`, the two-signal hypotheses hold, yet the worst case `253/50` exceeds
`ℓ*(absolute) = 243/50` — because `δ > π*(1) − q = 1/20` and `λ = 23/50 ≥ q`.
Source: mandate T17(b) (finding about the mandate's derivation)
Kind: N+ (refutation of the unconditional rule)
Fidelity: exact
Hyps: (a) only -/
theorem mandate_rule_refuted :
    (1 / 10 : ℝ) < maxSafeDelta cxLaw 9 11 ∧ piStar cxLaw true - qk 9 11 0 < 1 / 10 ∧
      qk 9 11 0 ≤ lam cxLaw ∧ worst cxLaw 9 11 (1 / 10) = 253 / 50 ∧
      loss cxLaw absoluteRule 9 11 0 = 243 / 50 ∧ ¬ worst cxLaw 9 11 (1 / 10) < loss cxLaw absoluteRule 9 11 0 := by
  obtain ⟨m1, m2, m3, m4⟩ := cxLaw_mass
  have hA0 : ¬ canAccept cxLaw 9 11 (1 / 10) false := by
    unfold canAccept; simp [qk, sigMass, m2, m4]; norm_num
  have hR0 : canResist cxLaw 9 11 (1 / 10) false := by
    unfold canResist; simp [qk, sigMass, m2, m4]; norm_num
  have hA1 : canAccept cxLaw 9 11 (1 / 10) true := by
    unfold canAccept; simp [qk, sigMass, m1, m3]; norm_num
  have hR1 : canResist cxLaw 9 11 (1 / 10) true := by
    unfold canResist; simp [qk, sigMass, m1, m3]; norm_num
  have hw : worst cxLaw 9 11 (1 / 10) = 253 / 50 := by
    simp only [worst, Fintype.sum_bool, worstAt, hA0, hR0, hA1, hR1, and_self, if_true, false_and, if_false,
      m1, m2, m3, m4]
    norm_num
  have habs : loss cxLaw absoluteRule 9 11 0 = 243 / 50 := by
    simp [loss, Fintype.sum_bool, cost, absoluteRule, m3, m4]; norm_num
  refine ⟨?_, ?_, ?_, hw, habs, ?_⟩
  · simp [maxSafeDelta, piStar, qk, sigMass, m2, m4]; norm_num
  · simp [piStar, qk, sigMass, m1, m3]; norm_num
  · simp [lam, qk, Fintype.sum_bool, m1, m2]; norm_num
  · rw [hw, habs]; norm_num

/-! ## The cells of `switch_rule.out` -/

/-- Toy T's detector law at legitimizing rate `λ`. Source: `switch_rule.py`. Kind: D. Fidelity: n/a -/
noncomputable def toyAt (lam : ℝ) (hl : lam ∈ Set.Icc (0 : ℝ) 1) : Distr (Bool × Bool) :=
  detectorLaw lam (1 / 10) (9 / 10) hl ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩

/-- `toyAt` masses and posteriors. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toyAt_mass (lam : ℝ) (hl : lam ∈ Set.Icc (0 : ℝ) 1) :
    legMass (toyAt lam hl) true = lam * (9 / 10) ∧ legMass (toyAt lam hl) false = lam * (1 / 10) ∧
      nonlegMass (toyAt lam hl) true = (1 - lam) * (1 / 10) ∧
      nonlegMass (toyAt lam hl) false = (1 - lam) * (9 / 10) := by
  simp [toyAt, detectorLaw, legMass, nonlegMass]; norm_num

/-- **The full hypothesis package of `two_signal_closed_form`** at `(λ, c, h)` on Toy T's detector law:
positive masses, `π*(0) < q ≤ π*(1)` (product form), and the side condition. A cell theorem that carries
it inhabits the closed form; one that only evaluates `maxSafeDelta` does not (audit r1, adversarial B1).
Source: [[corr-wf14b-2-inventory]] 2-005; mandate T17(b)
Kind: D
Fidelity: exact -/
def cellPkg (l c h : ℝ) (hl : l ∈ Set.Icc (0 : ℝ) 1) : Prop :=
  0 < sigMass (toyAt l hl) false ∧ 0 < sigMass (toyAt l hl) true ∧
    legMass (toyAt l hl) false < qk c h 0 * sigMass (toyAt l hl) false ∧
    qk c h 0 * sigMass (toyAt l hl) true ≤ legMass (toyAt l hl) true ∧
    (maxSafeDelta (toyAt l hl) c h ≤ piStar (toyAt l hl) true - qk c h 0 ∨ lam (toyAt l hl) < qk c h 0)

/-- **An exact value cell**: at `(λ, c, h)` on Toy T, for every `δ ≥ 0` the conditioned row beats absolute
in the worst case iff `δ < x` — the whole content of a tabulated max-safe-`δ` value `x`.
Source: [[corr-wf14b-2-inventory]] 2-005 / `switch_rule.out`
Kind: D
Fidelity: exact -/
def cellExact (l c h x : ℝ) (hl : l ∈ Set.Icc (0 : ℝ) 1) : Prop :=
  ∀ δ, 0 ≤ δ → (worst (toyAt l hl) c h δ < loss (toyAt l hl) absoluteRule c h 0 ↔ δ < x)

/-- **A "none" cell**: at `(λ, c, h)` on Toy T no `δ ≥ 0` makes the conditioned row beat absolute in the
worst case.
Source: [[corr-wf14b-2-inventory]] 2-005 / `switch_rule.out` ("none")
Kind: D
Fidelity: exact -/
def cellNone (l c h : ℝ) (hl : l ∈ Set.Icc (0 : ℝ) 1) : Prop :=
  ∀ δ, 0 ≤ δ → loss (toyAt l hl) absoluteRule c h 0 ≤ worst (toyAt l hl) c h δ

/-- A cell with the package and `maxSafeDelta = x` is exact at `x` (`two_signal_closed_form`).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cellExact_of_pkg (l c h x : ℝ) (hl : l ∈ Set.Icc (0 : ℝ) 1) (hch : 0 < c + h)
    (hpkg : cellPkg l c h hl) (hx : maxSafeDelta (toyAt l hl) c h = x) : cellExact l c h x hl := by
  intro δ hδ
  rw [← hx]
  obtain ⟨h1, h2, h3, h4, h5⟩ := hpkg
  exact two_signal_closed_form _ hch h1 h2 h3 h4 h5 δ hδ

/-- A cell where every positive-mass posterior is `≥ q` is a "none" cell (`worst_ge_absolute`).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cellNone_of_all_ge (l c h : ℝ) (hl : l ∈ Set.Icc (0 : ℝ) 1)
    (hall : ∀ s, 0 < sigMass (toyAt l hl) s → qk c h 0 * sigMass (toyAt l hl) s ≤ legMass (toyAt l hl) s) :
    cellNone l c h hl :=
  fun δ hδ => worst_ge_absolute _ c h δ hδ hall

/-- **Pause stakes `c = 1`, `h = 4`** (the six rows of `switch_rule.out`'s pause block): the exact rule is
`δ < 77/410, 17/110, 1/10` at `λ = 1/10, 3/10, 1/2` — each cell carrying the full package of
`two_signal_closed_form` — and no safe `δ` at `λ = 7/10, 9/10, 19/20` (`π*(0) ≥ q`, so every posterior
is `≥ q`).
Source: [[corr-wf14b-2-inventory]] 2-005 / `switch_rule.out` (pause block)
Kind: N+ (the closed form inhabited per cell)
Fidelity: exact (the script's `0.1875, 0.1525, 0.0975` are the grid values below these)
Hyps: (a) only -/
theorem pause_cells :
    cellExact (1 / 10) 1 4 (77 / 410) ⟨by norm_num, by norm_num⟩ ∧
      cellExact (3 / 10) 1 4 (17 / 110) ⟨by norm_num, by norm_num⟩ ∧
      cellExact (1 / 2) 1 4 (1 / 10) ⟨by norm_num, by norm_num⟩ ∧
      cellNone (7 / 10) 1 4 ⟨by norm_num, by norm_num⟩ ∧
      cellNone (9 / 10) 1 4 ⟨by norm_num, by norm_num⟩ ∧
      cellNone (19 / 20) 1 4 ⟨by norm_num, by norm_num⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine cellExact_of_pkg _ _ _ _ _ (by norm_num) ?_ ?_ <;>
      simp [cellPkg, maxSafeDelta, piStar, lam, qk, sigMass, toyAt, detectorLaw, legMass, nonlegMass,
        Fintype.sum_bool] <;> norm_num
  · refine cellExact_of_pkg _ _ _ _ _ (by norm_num) ?_ ?_ <;>
      simp [cellPkg, maxSafeDelta, piStar, lam, qk, sigMass, toyAt, detectorLaw, legMass, nonlegMass,
        Fintype.sum_bool] <;> norm_num
  · refine cellExact_of_pkg _ _ _ _ _ (by norm_num) ?_ ?_ <;>
      simp [cellPkg, maxSafeDelta, piStar, lam, qk, sigMass, toyAt, detectorLaw, legMass, nonlegMass,
        Fintype.sum_bool] <;> norm_num
  all_goals
    refine cellNone_of_all_ge _ _ _ _ ?_
    intro s _
    cases s <;> simp [qk, sigMass, toyAt, detectorLaw, legMass, nonlegMass] <;> norm_num

/-- **`c = h = 1`** (six rows): the exact rule is `δ < 20/41, 5/11, 2/5, 5/17` at `λ = 1/10, 3/10, 1/2,
7/10`, each with the full package, and none at `λ = 9/10, 19/20`.
Source: [[corr-wf14b-2-inventory]] 2-005 / `switch_rule.out` (`c=h=1` block)
Kind: N+ (the closed form inhabited per cell)
Fidelity: exact
Hyps: (a) only -/
theorem unit_cells :
    cellExact (1 / 10) 1 1 (20 / 41) ⟨by norm_num, by norm_num⟩ ∧
      cellExact (3 / 10) 1 1 (5 / 11) ⟨by norm_num, by norm_num⟩ ∧
      cellExact (1 / 2) 1 1 (2 / 5) ⟨by norm_num, by norm_num⟩ ∧
      cellExact (7 / 10) 1 1 (5 / 17) ⟨by norm_num, by norm_num⟩ ∧
      cellNone (9 / 10) 1 1 ⟨by norm_num, by norm_num⟩ ∧
      cellNone (19 / 20) 1 1 ⟨by norm_num, by norm_num⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine cellExact_of_pkg _ _ _ _ _ (by norm_num) ?_ ?_ <;>
      simp [cellPkg, maxSafeDelta, piStar, lam, qk, sigMass, toyAt, detectorLaw, legMass, nonlegMass,
        Fintype.sum_bool] <;> norm_num
  · refine cellExact_of_pkg _ _ _ _ _ (by norm_num) ?_ ?_ <;>
      simp [cellPkg, maxSafeDelta, piStar, lam, qk, sigMass, toyAt, detectorLaw, legMass, nonlegMass,
        Fintype.sum_bool] <;> norm_num
  · refine cellExact_of_pkg _ _ _ _ _ (by norm_num) ?_ ?_ <;>
      simp [cellPkg, maxSafeDelta, piStar, lam, qk, sigMass, toyAt, detectorLaw, legMass, nonlegMass,
        Fintype.sum_bool] <;> norm_num
  · refine cellExact_of_pkg _ _ _ _ _ (by norm_num) ?_ ?_ <;>
      simp [cellPkg, maxSafeDelta, piStar, lam, qk, sigMass, toyAt, detectorLaw, legMass, nonlegMass,
        Fintype.sum_bool] <;> norm_num
  all_goals
    refine cellNone_of_all_ge _ _ _ _ ?_
    intro s _
    cases s <;> simp [qk, sigMass, toyAt, detectorLaw, legMass, nonlegMass] <;> norm_num

/-- **Whole-line stakes `(9/10, 11/10)`** (six rows): the exact rule is `δ < 359/820, 89/220, 7/20, 83/340`
at `λ = 1/10, 3/10, 1/2, 7/10`, each with the full package, and none at `λ = 9/10, 19/20`.
Source: [[corr-wf14b-2-inventory]] 2-005 / `switch_rule.out` (whole-line block)
Kind: N+ (the closed form inhabited per cell)
Fidelity: exact
Hyps: (a) only -/
theorem wholeLine_cells :
    cellExact (1 / 10) (9 / 10) (11 / 10) (359 / 820) ⟨by norm_num, by norm_num⟩ ∧
      cellExact (3 / 10) (9 / 10) (11 / 10) (89 / 220) ⟨by norm_num, by norm_num⟩ ∧
      cellExact (1 / 2) (9 / 10) (11 / 10) (7 / 20) ⟨by norm_num, by norm_num⟩ ∧
      cellExact (7 / 10) (9 / 10) (11 / 10) (83 / 340) ⟨by norm_num, by norm_num⟩ ∧
      cellNone (9 / 10) (9 / 10) (11 / 10) ⟨by norm_num, by norm_num⟩ ∧
      cellNone (19 / 20) (9 / 10) (11 / 10) ⟨by norm_num, by norm_num⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine cellExact_of_pkg _ _ _ _ _ (by norm_num) ?_ ?_ <;>
      simp [cellPkg, maxSafeDelta, piStar, lam, qk, sigMass, toyAt, detectorLaw, legMass, nonlegMass,
        Fintype.sum_bool] <;> norm_num
  · refine cellExact_of_pkg _ _ _ _ _ (by norm_num) ?_ ?_ <;>
      simp [cellPkg, maxSafeDelta, piStar, lam, qk, sigMass, toyAt, detectorLaw, legMass, nonlegMass,
        Fintype.sum_bool] <;> norm_num
  · refine cellExact_of_pkg _ _ _ _ _ (by norm_num) ?_ ?_ <;>
      simp [cellPkg, maxSafeDelta, piStar, lam, qk, sigMass, toyAt, detectorLaw, legMass, nonlegMass,
        Fintype.sum_bool] <;> norm_num
  · refine cellExact_of_pkg _ _ _ _ _ (by norm_num) ?_ ?_ <;>
      simp [cellPkg, maxSafeDelta, piStar, lam, qk, sigMass, toyAt, detectorLaw, legMass, nonlegMass,
        Fintype.sum_bool] <;> norm_num
  all_goals
    refine cellNone_of_all_ge _ _ _ _ ?_
    intro s _
    cases s <;> simp [qk, sigMass, toyAt, detectorLaw, legMass, nonlegMass] <;> norm_num

/-- **The grid finding**: the voice's `0.1875, 0.1525, 0.0975` are the largest multiples of `1/400`
strictly below the exact bounds `77/410, 17/110, 1/10` (`switch_rule.py` scans `F(i, 400)` and keeps the
last `i` with `worst < abs`; at `δ = 1/10 = 40/400` exactly the worst case equals the absolute row).
Source: [[corr-wf14b-2-inventory]] 2-005 / `switch_rule.py` (`max_safe_delta`, `grid=400`); hudson-voice.md
item 2
Kind: N+ (presentation finding)
Fidelity: exact
Hyps: (a) only -/
theorem grid_values :
    ((75 / 400 : ℝ) < 77 / 410 ∧ (77 / 410 : ℝ) ≤ 76 / 400) ∧
      ((61 / 400 : ℝ) < 17 / 110 ∧ (17 / 110 : ℝ) ≤ 62 / 400) ∧
      ((39 / 400 : ℝ) < 1 / 10 ∧ (1 / 10 : ℝ) ≤ 40 / 400) := by
  norm_num

end Switch

end Cleanroom.Corrigibility.CorrLandscape
