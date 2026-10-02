import Cleanroom.Corrigibility.CorrLandscape.Map
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# `corr-landscape` — `Trichotomy`: Statement 3, the exact trichotomy (T14, load-bearing 3)

For a rule `r` with resist set `R = {s : r s}` and adopt set `A` its complement, the signed masses
`D_R = ∑_{s ∈ R} (μ(s, L) − q_k P*(s))`, `D_A` likewise, and the three identities of
`landscape-final.md` Statement 3 / P3 ([[corr-wf14b-inventory]] 063):

* `ℓ*(r) − ℓ*(none) = −(c + h) D_A`, `ℓ*(r) − ℓ*(absolute) = (c + h) D_R`, `λ − q_k = D_A + D_R`;
* (a) `r` weakly dominates both constants iff `D_R ≤ 0 ∧ 0 ≤ D_A` — the source's `π̄_R ≤ q_k ≤ π̄_A`
  with the averages replaced by signed masses (equivalent when `p_R, p_A > 0`, since
  `D_R = p_R (π̄_R − q_k)`);
* (b) **aggregate anti-informativeness** `D_R/p_R > D_A/p_A` (in product form `D_R p_A > D_A p_R`
  with `p_R, p_A > 0`) implies `ℓ*(r) > min(ℓ*(absolute), ℓ*(none))`, with the source's three-case
  refinement (`anti_informative_cases`).

Toy T's three uncovered models at `λ = 1/2` are the N+ cells (over-trust loss `1/2`, under-trust `2`,
anti-informative `9/4 > max(1/2, 2)`), on the detector law `detectorLaw λ α_L β_L`.
-/

namespace Cleanroom.Corrigibility.CorrLandscape

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

set_option linter.unusedSectionVars false

namespace Trichotomy

open Map

variable {S : Type} [Fintype S] [DecidableEq S]

/-- The signed legitimacy mass of a signal relative to the threshold: `μ(s, L) − q_k P*(s)`
(`= P*(s)(π*(s) − q_k)` on the support).
Source: [[corr-wf14b-inventory]] 063 / landscape-final.md S5 ("write `D_R := p_R(π̄_R − q_k)`")
Kind: D
Fidelity: exact (product form) -/
noncomputable def signed (μ : Distr (S × Bool)) (c h k : ℝ) (s : S) : ℝ :=
  legMass μ s - qk c h k * sigMass μ s

/-- `D_R`: the signed mass over the resist set.
Source: [[corr-wf14b-inventory]] 063 / landscape-final.md S5
Kind: D
Fidelity: exact (product form) -/
noncomputable def DR (μ : Distr (S × Bool)) (r : S → Bool) (c h k : ℝ) : ℝ :=
  ∑ s ∈ univ.filter (fun s => r s = true), signed μ c h k s

/-- `D_A`: the signed mass over the adopt set.
Source: [[corr-wf14b-inventory]] 063 / landscape-final.md S5
Kind: D
Fidelity: exact (product form) -/
noncomputable def DA (μ : Distr (S × Bool)) (r : S → Bool) (c h k : ℝ) : ℝ :=
  ∑ s ∈ univ.filter (fun s => r s = false), signed μ c h k s

/-- `p_R`: the mass of the resist set.
Source: [[corr-wf14b-inventory]] 063 / landscape-final.md S5
Kind: D
Fidelity: exact -/
def pR (μ : Distr (S × Bool)) (r : S → Bool) : ℝ := ∑ s ∈ univ.filter (fun s => r s = true), sigMass μ s

/-- `p_A`: the mass of the adopt set.
Source: [[corr-wf14b-inventory]] 063 / landscape-final.md S5
Kind: D
Fidelity: exact -/
def pA (μ : Distr (S × Bool)) (r : S → Bool) : ℝ := ∑ s ∈ univ.filter (fun s => r s = false), sigMass μ s

/-! ## The three identities (P3) -/

/-- **Identity 1**: `ℓ*(r) − ℓ*(none) = −(c + h) D_A`.
Source: [[corr-wf14b-inventory]] 063 / landscape-final.md Statement 3, P3
Kind: P
Fidelity: exact
Hyps: (a) `0 < c + h` -/
theorem loss_sub_none (μ : Distr (S × Bool)) (r : S → Bool) {c h : ℝ} (k : ℝ) (hch : 0 < c + h) :
    loss μ r c h k - loss μ noneRule c h k = -((c + h) * DA μ r c h k) := by
  unfold loss DA
  rw [sum_filter, ← sum_sub_distrib, mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun s _ => ?_
  have key := cost_true_sub_false μ k hch s
  unfold signed noneRule
  cases hr : r s
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.true_eq_false, if_true]
    linarith
  · simp

/-- **Identity 2**: `ℓ*(r) − ℓ*(absolute) = (c + h) D_R`.
Source: [[corr-wf14b-inventory]] 063 / landscape-final.md Statement 3, P3
Kind: P
Fidelity: exact
Hyps: (a) `0 < c + h` -/
theorem loss_sub_absolute (μ : Distr (S × Bool)) (r : S → Bool) {c h : ℝ} (k : ℝ) (hch : 0 < c + h) :
    loss μ r c h k - loss μ absoluteRule c h k = (c + h) * DR μ r c h k := by
  unfold loss DR
  rw [sum_filter, ← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun s _ => ?_
  have key := cost_true_sub_false μ k hch s
  unfold signed absoluteRule
  cases hr : r s
  · simp
  · simp only [↓reduceIte]
    linarith

/-- **Identity 3**: `λ − q_k = D_A + D_R`.
Source: [[corr-wf14b-inventory]] 063 / landscape-final.md Statement 3, P3
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem lam_sub_qk (μ : Distr (S × Bool)) (r : S → Bool) (c h k : ℝ) :
    lam μ - qk c h k = DA μ r c h k + DR μ r c h k := by
  unfold DA DR
  have hsplit := sum_filter_add_sum_filter_not univ (fun s => r s = false) (signed μ c h k)
  have hnot : univ.filter (fun s => ¬ r s = false) = univ.filter (fun s => r s = true) := by
    ext s; simp
  rw [hnot] at hsplit
  rw [hsplit]
  unfold signed
  rw [sum_sub_distrib, ← mul_sum, sum_sigMass, mul_one]
  rfl

/-! ## (a) weak domination of both constants -/

/-- **Statement 3(a)**: `r` weakly dominates both constants iff `D_R ≤ 0 ∧ 0 ≤ D_A` (the source's
`π̄_R ≤ q_k ≤ π̄_A` in signed-mass form).
Source: [[corr-wf14b-inventory]] 063 / landscape-final.md Statement 3(a), P3
Kind: P
Fidelity: variant: averages replaced by signed masses (equivalent when `p_R, p_A > 0`; the signed form
needs no positivity)
Hyps: (a) `0 < c + h` -/
theorem dominates_both_iff (μ : Distr (S × Bool)) (r : S → Bool) {c h : ℝ} (k : ℝ) (hch : 0 < c + h) :
    (loss μ r c h k ≤ loss μ absoluteRule c h k ∧ loss μ r c h k ≤ loss μ noneRule c h k) ↔
      (DR μ r c h k ≤ 0 ∧ 0 ≤ DA μ r c h k) := by
  have h1 := loss_sub_absolute μ r k hch
  have h2 := loss_sub_none μ r k hch
  constructor
  · rintro ⟨ha, hn⟩
    constructor
    · by_contra hcon
      rw [not_le] at hcon
      nlinarith [mul_pos hch hcon]
    · by_contra hcon
      rw [not_le] at hcon
      nlinarith [mul_pos hch (neg_pos.2 hcon)]
  · rintro ⟨hR, hA⟩
    constructor
    · nlinarith [mul_nonneg hch.le (neg_nonneg.2 hR)]
    · nlinarith [mul_nonneg hch.le hA]

/-! ## (b) aggregate anti-informativeness is strictly worse than the better constant -/

/-- **Statement 3(b), the trichotomy**: under `p_R, p_A > 0` and aggregate anti-informativeness
`D_R p_A > D_A p_R` (i.e. `D_R/p_R > D_A/p_A`), the rule is strictly worse than the better constant.
Source: [[corr-wf14b-inventory]] 063 / landscape-final.md Statement 3(b), P3
Kind: P
Fidelity: exact (hypotheses: nonempty resist and adopt sets with positive mass, as the source's `R, A`
non-empty; with `R` or `A` empty `r` is a constant and (b) is vacuous)
Hyps: (a) only -/
theorem anti_informative_worse (μ : Distr (S × Bool)) (r : S → Bool) {c h : ℝ} (k : ℝ) (hch : 0 < c + h)
    (hpR : 0 < pR μ r) (hpA : 0 < pA μ r)
    (hanti : DA μ r c h k * pR μ r < DR μ r c h k * pA μ r) :
    min (loss μ absoluteRule c h k) (loss μ noneRule c h k) < loss μ r c h k := by
  have h1 := loss_sub_absolute μ r k hch
  have h2 := loss_sub_none μ r k hch
  rw [min_lt_iff]
  by_cases hA : 0 ≤ DA μ r c h k
  · left
    have hR : 0 < DR μ r c h k := by
      by_contra hcon
      rw [not_lt] at hcon
      nlinarith [mul_nonneg hA hpR.le, mul_nonneg (neg_nonneg.2 hcon) hpA.le]
    nlinarith [mul_pos hch hR]
  · right
    rw [not_le] at hA
    nlinarith [mul_pos hch (neg_pos.2 hA)]

/-- **Statement 3(b), the three cases of P3**: under the same hypotheses, either `D_A ≥ 0` (then
absolute is the better constant and `r` is strictly worse than it), or `D_A < 0 ∧ D_R ≤ 0` (none is the
better constant and `r` is strictly worse than it), or `D_A < 0 ∧ D_R > 0` (`r` is worse than both).
Source: [[corr-wf14b-inventory]] 063 / landscape-final.md P3 (the three cases)
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem anti_informative_cases (μ : Distr (S × Bool)) (r : S → Bool) {c h : ℝ} (k : ℝ) (hch : 0 < c + h)
    (hpR : 0 < pR μ r) (hpA : 0 < pA μ r)
    (hanti : DA μ r c h k * pR μ r < DR μ r c h k * pA μ r) :
    (0 ≤ DA μ r c h k ∧ loss μ absoluteRule c h k < loss μ noneRule c h k ∧
        loss μ absoluteRule c h k < loss μ r c h k) ∨
      (DA μ r c h k < 0 ∧ DR μ r c h k ≤ 0 ∧ loss μ noneRule c h k < loss μ absoluteRule c h k ∧
        loss μ noneRule c h k < loss μ r c h k) ∨
      (DA μ r c h k < 0 ∧ 0 < DR μ r c h k ∧ loss μ absoluteRule c h k < loss μ r c h k ∧
        loss μ noneRule c h k < loss μ r c h k) := by
  have h1 := loss_sub_absolute μ r k hch
  have h2 := loss_sub_none μ r k hch
  have h3 := lam_sub_qk μ r c h k
  have hal := absolute_lt_none_iff μ k hch
  by_cases hA : 0 ≤ DA μ r c h k
  · left
    have hR : 0 < DR μ r c h k := by
      by_contra hcon
      rw [not_lt] at hcon
      nlinarith [mul_nonneg hA hpR.le, mul_nonneg (neg_nonneg.2 hcon) hpA.le]
    refine ⟨hA, hal.2 (by linarith), by nlinarith [mul_pos hch hR]⟩
  · rw [not_le] at hA
    by_cases hR : DR μ r c h k ≤ 0
    · right; left
      refine ⟨hA, hR, ?_, by nlinarith [mul_pos hch (neg_pos.2 hA)]⟩
      have : lam μ < qk c h k := by linarith
      rw [loss_absolute, loss_none, qk, lt_div_iff₀ hch] at *
      nlinarith
    · right; right
      rw [not_le] at hR
      exact ⟨hA, hR, by nlinarith [mul_pos hch hR], by nlinarith [mul_pos hch (neg_pos.2 hA)]⟩

/-! ## Toy T: the detector law and the three uncovered models (P7) -/

/-- **Toy T's law**: legitimizing rate `λ`, a two-valued legitimacy detector with `P(s = 1 ∣ L) = β_L`,
`P(s = 1 ∣ ¬L) = α_L`; the signal `true` is `s = 1`.
Source: [[corr-wf14b-inventory]] 061, 063 / landscape-final.md D3, P7 ("detector `(0.1, 0.9)`")
Kind: D
Fidelity: exact -/
noncomputable def detectorLaw (lam αL βL : ℝ) (hl : lam ∈ Set.Icc (0 : ℝ) 1) (ha : αL ∈ Set.Icc (0 : ℝ) 1)
    (hb : βL ∈ Set.Icc (0 : ℝ) 1) : Distr (Bool × Bool) where
  mass p := match p with
    | (true, true) => lam * βL
    | (false, true) => lam * (1 - βL)
    | (true, false) => (1 - lam) * αL
    | (false, false) => (1 - lam) * (1 - αL)
  nonneg p := by
    rcases p with ⟨s, l⟩
    cases s <;> cases l <;> simp <;> nlinarith [hl.1, hl.2, ha.1, ha.2, hb.1, hb.2]
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    ring

/-- The worked mixed column of Toy T: `λ = 1/2`, detector `(1/10, 9/10)`.
Source: [[corr-wf14b-inventory]] 063 / landscape-final.md P7 ("Mixed")
Kind: D
Fidelity: n/a (witness) -/
noncomputable def toyMixed : Distr (Bool × Bool) :=
  detectorLaw (1 / 2) (1 / 10) (9 / 10) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩

/-- `toyMixed` masses. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toyMixed_mass : legMass toyMixed true = 9 / 20 ∧ legMass toyMixed false = 1 / 20 ∧
    nonlegMass toyMixed true = 1 / 20 ∧ nonlegMass toyMixed false = 9 / 20 := by
  simp [toyMixed, detectorLaw, legMass, nonlegMass]; norm_num

/-- **Toy T, the constants and Bayes at `λ = 1/2`**: `ℓ*(absolute) = 1/2`, `ℓ*(none) = 2`,
`ℓ*(Bayes) = 1/4`; the posteriors are `π*(0) = 1/10`, `π*(1) = 9/10`.
Source: [[corr-wf14b-inventory]] 062, 063 / landscape-final.md P7 ("Mixed: absolute 0.5, none 2.0,
covered-C 0.25")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem toyMixed_cells :
    loss toyMixed absoluteRule 1 4 0 = 1 / 2 ∧ loss toyMixed noneRule 1 4 0 = 2 ∧
      loss toyMixed (bayesRule toyMixed 1 4 0) 1 4 0 = 1 / 4 ∧
      piStar toyMixed false = 1 / 10 ∧ piStar toyMixed true = 9 / 10 := by
  obtain ⟨h1, h2, h3, h4⟩ := toyMixed_mass
  have hb1 : bayesRule toyMixed 1 4 0 true = false := by
    simp [bayesRule, qk, sigMass, h1, h3]; norm_num
  have hb0 : bayesRule toyMixed 1 4 0 false = true := by
    simp [bayesRule, qk, sigMass, h2, h4]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [loss_absolute]; simp [lam, Fintype.sum_bool, h1, h2]; norm_num
  · rw [loss_none]; simp [lam, Fintype.sum_bool, h1, h2]; norm_num
  · simp [loss, Fintype.sum_bool, hb1, hb0, cost, sigMass, h1, h2, h3, h4]; norm_num
  · simp [piStar, sigMass, h2, h4]; norm_num
  · simp [piStar, sigMass, h1, h3]; norm_num

/-- The over-trusting model `(λ̂, α̂, β̂) = (19/20, 1/2, 1/2)`: credence `19/20` at both signals.
Source: landscape-final.md P7 ("over-trust `(0.95, 0.5, 0.5)`")
Kind: D
Fidelity: n/a (witness) -/
noncomputable def overTrustCred : Bool → ℝ := fun _ => 19 / 20

/-- The under-trusting model `(1/20, 1/2, 1/2)`: credence `1/20` at both signals.
Source: landscape-final.md P7 ("under-trust `(0.05, 0.5, 0.5)`")
Kind: D
Fidelity: n/a (witness) -/
noncomputable def underTrustCred : Bool → ℝ := fun _ => 1 / 20

/-- The anti-informative objective law: `λ = 1/2` with the detector inverted, `(9/10, 1/10)`.
Source: landscape-final.md P7 ("anti-informative believes `(0.1, 0.9)` against objective `(0.9, 0.1)`")
Kind: D
Fidelity: n/a (witness) -/
noncomputable def toyInverted : Distr (Bool × Bool) :=
  detectorLaw (1 / 2) (9 / 10) (1 / 10) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩

/-- `toyInverted` masses. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toyInverted_mass : legMass toyInverted true = 1 / 20 ∧ legMass toyInverted false = 9 / 20 ∧
    nonlegMass toyInverted true = 9 / 20 ∧ nonlegMass toyInverted false = 1 / 20 := by
  simp [toyInverted, detectorLaw, legMass, nonlegMass]; norm_num

/-- **Toy T, the three uncovered models (N+ for Statement 3)**: over-trust pays `1/2`, under-trust `2`,
and the anti-informative agent (believing the covered posteriors `1/10, 9/10` against the inverted
objective law) pays `9/4 > max(1/2, 2)` — strictly worse than both constants, as Statement 3(b)
predicts: its signed masses are `D_R = 7/20`, `D_A = −1/20` with `p_R = p_A = 1/2`.
Source: [[corr-wf14b-inventory]] 063 / landscape-final.md P7, Statement 7 ("C × mixed × uncovered")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem toy_uncovered_cells :
    loss toyMixed (conditionedRule overTrustCred 0 1 4) 1 4 0 = 1 / 2 ∧
      loss toyMixed (conditionedRule underTrustCred 0 1 4) 1 4 0 = 2 ∧
      loss toyInverted (conditionedRule (piStar toyMixed) 0 1 4) 1 4 0 = 9 / 4 ∧
      DR toyInverted (conditionedRule (piStar toyMixed) 0 1 4) 1 4 0 = 7 / 20 ∧
      DA toyInverted (conditionedRule (piStar toyMixed) 0 1 4) 1 4 0 = -(1 / 20) ∧
      pR toyInverted (conditionedRule (piStar toyMixed) 0 1 4) = 1 / 2 ∧
      pA toyInverted (conditionedRule (piStar toyMixed) 0 1 4) = 1 / 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := toyMixed_mass
  obtain ⟨i1, i2, i3, i4⟩ := toyInverted_mass
  obtain ⟨-, -, -, p0, p1⟩ := toyMixed_cells
  have ho : ∀ s, conditionedRule overTrustCred 0 1 4 s = false := by
    intro s; simp [conditionedRule, overTrustCred, qk]; norm_num
  have hu : ∀ s, conditionedRule underTrustCred 0 1 4 s = true := by
    intro s; simp [conditionedRule, underTrustCred, qk]; norm_num
  have ha1 : conditionedRule (piStar toyMixed) 0 1 4 true = false := by
    simp [conditionedRule, p1, qk]; norm_num
  have ha0 : conditionedRule (piStar toyMixed) 0 1 4 false = true := by
    simp [conditionedRule, p0, qk]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [loss, Fintype.sum_bool, ho, cost, h3, h4]; norm_num
  · simp [loss, Fintype.sum_bool, hu, cost, sigMass, h1, h2, h3, h4]; norm_num
  · simp [loss, Fintype.sum_bool, ha1, ha0, cost, sigMass, i1, i2, i3, i4]; norm_num
  · simp [DR, signed, Fintype.sum_bool, ha1, ha0, qk, sigMass, i1, i2, i3, i4, filter_true_of_mem,
      Finset.sum_filter]
    norm_num
  · simp [DA, signed, Fintype.sum_bool, ha1, ha0, qk, sigMass, i1, i2, i3, i4, Finset.sum_filter]
    norm_num
  · simp [pR, Fintype.sum_bool, ha1, ha0, sigMass, i1, i2, i3, i4, Finset.sum_filter]; norm_num
  · simp [pA, Fintype.sum_bool, ha1, ha0, sigMass, i1, i2, i3, i4, Finset.sum_filter]; norm_num

/-- **The anti-informative cell inhabits Statement 3(b)'s full hypothesis package** and the conclusion
is the predicted one: `9/4 > min(1/2, 2)`.
Source: [[corr-wf14b-inventory]] 063 / landscape-final.md Statement 3(b), P7
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem toy_anti_informative_instance :
    0 < pR toyInverted (conditionedRule (piStar toyMixed) 0 1 4) ∧
      0 < pA toyInverted (conditionedRule (piStar toyMixed) 0 1 4) ∧
      DA toyInverted (conditionedRule (piStar toyMixed) 0 1 4) 1 4 0 *
          pR toyInverted (conditionedRule (piStar toyMixed) 0 1 4) <
        DR toyInverted (conditionedRule (piStar toyMixed) 0 1 4) 1 4 0 *
          pA toyInverted (conditionedRule (piStar toyMixed) 0 1 4) ∧
      min (loss toyInverted absoluteRule 1 4 0) (loss toyInverted noneRule 1 4 0) <
        loss toyInverted (conditionedRule (piStar toyMixed) 0 1 4) 1 4 0 := by
  obtain ⟨-, -, l94, dR, dA, pr, pa⟩ := toy_uncovered_cells
  refine ⟨by rw [pr]; norm_num, by rw [pa]; norm_num, by rw [dR, dA, pr, pa]; norm_num, ?_⟩
  exact anti_informative_worse toyInverted _ 0 (by norm_num) (by rw [pr]; norm_num)
    (by rw [pa]; norm_num) (by rw [dR, dA, pr, pa]; norm_num)

end Trichotomy

end Cleanroom.Corrigibility.CorrLandscape
