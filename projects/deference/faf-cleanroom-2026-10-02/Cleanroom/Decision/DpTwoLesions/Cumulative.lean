import Cleanroom.Decision.DpTwoLesions.InteriorReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.Irrational

/-!
# T8 — Proposition 5: the cumulative learner, on the recursion

Two lemmas on the deterministic recursion `x_{t+1} = x_t + (b_t − x_t)/(t+2)`, `b_t ∈ {0, 1}`
(indexing disclosed: `x₀` is the initial policy carried with weight one, so `x_t` is the mean
of `x₀, b₀, …, b_{t−1}`; the doc's `/(t+1)` with `t ≥ 1` is the same recursion shifted): (L1)
if `b ≡ 0` from `t₀` then `x_t = x_{t₀}(t₀+1)/(t+1) → 0`, and if `b ≡ 1` then `1 − x_t → 0`;
(L2) **the band**: under a threshold rule `b_t = 1 ↔ x_t < θ`, `|x_t − θ| ≤ 1/(t+1)` for every
`t`, so `x_t → θ`. Then Proposition 5: `prop5_strong` (no interior fixed point: `x_t → 0` from
every start) and `prop5_weak` (three fixed points `0 < p̌ < p̂ < 1`: `x_t → 0` from `x₀ < p̌`;
`x_t → p̂` from `x₀ ∈ (p̌, p̂)` **provided `p̂ − p̌ > 1/3`** (`prop5_weak_between`), and from
`x₀ > p̂` provided `p̂ − p̌ > 1/2` (`prop5_weak_above`)). None of the three Proposition 5
theorems carries (H): the regime hypothesis (`Q > 0` on `[0, 1]`, or two roots `0 < p̌ < p̂ < 1`)
is what bites (audit r1). The gap condition is not decoration: **the doc's clause "`p̄_t → p̂`
when `p̄₀ > p̌`" is false as stated** — at the doc's parameters with `δ = 139/5000` (just below
`δ*`) the trajectory from `x₀ = 33/50 ∈ (p̌, p̂)` overshoots past `p̂` at step 1 (the early
steps are large), falls below `p̌` at step 2 and converges to `0` (`prop5_refuted_overshoot`).
The doc's proof is an Euler-scheme heuristic that ignores the step size. Outside (H) (`sessP`):
the smoke label is a fixed point, the unique interior crossing `p*` is bracketed in
`(0.0201, 0.0202)`, and every trajectory from `x₀ > p*` converges to `1`
(`prop5_outsideH_smokes`). The no-tie hypothesis is **discharged** at the doc's `δ = 1/100` by
irrationality: `noTie_of_rat_at_doc` proves, for every cumulative trajectory from a rational
start, that every `x_t` is rational and never ties (one induction alternating rational ⇒ no tie
⇒ pure best response ⇒ rational), and `prop5_weak_between_at_doc` is the hypothesis-free
instance of the basin theorem there (the witness for `prop5_weak_between`'s full package).
Serves [[dp-two-lesions-mandate]] T8 (dp-core-078, 2-009(a)(d)).
-/

namespace Cleanroom.Decision.DpTwoLesions

open Set Filter Topology

/-! ## The recursion -/

/-- One step of the cumulative recursion. Source: doc §5. Kind: D -/
noncomputable def cumulStep (t : ℕ) (x b : ℝ) : ℝ := x + (b - x) / (t + 2)

/-- **(L1) `b ≡ 0` from `t₀`**: `x_t = x_{t₀} (t₀ + 1)/(t + 1)` for `t ≥ t₀`.
Source: [[two-lesions-doc-2026-09-18]] §5 Proposition 5 proof ("`p̄` decreases to `0`"), made
exact on the recursion
Kind: P
Fidelity: exact
Hyps: none -/
theorem cumul_zero_from {x : ℕ → ℝ} {t₀ : ℕ}
    (h : ∀ t, t₀ ≤ t → x (t + 1) = cumulStep t (x t) 0) :
    ∀ t, t₀ ≤ t → x t = x t₀ * (t₀ + 1) / (t + 1) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => field_simp
  | succ t ht ih =>
    rw [h t ht, cumulStep, ih]
    have h1 : (t : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (t : ℝ) + 2 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- **(L1′) `b ≡ 1` from `t₀`**: `1 − x_t = (1 − x_{t₀})(t₀ + 1)/(t + 1)` for `t ≥ t₀`.
Source: [[two-lesions-doc-2026-09-18]] §5 Proposition 5 proof ("`p̄` increases")
Kind: P
Fidelity: exact
Hyps: none -/
theorem cumul_one_from {x : ℕ → ℝ} {t₀ : ℕ}
    (h : ∀ t, t₀ ≤ t → x (t + 1) = cumulStep t (x t) 1) :
    ∀ t, t₀ ≤ t → 1 - x t = (1 - x t₀) * (t₀ + 1) / (t + 1) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => field_simp
  | succ t ht ih =>
    rw [h t ht, cumulStep]
    have h1 : (t : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (t : ℝ) + 2 ≠ 0 := by positivity
    have : x t = 1 - (1 - x t₀) * (t₀ + 1) / (t + 1) := by linarith
    rw [this]
    push_cast
    field_simp
    ring

/-- `c/(t + 1) → 0`. Source: none: infrastructure. Kind: L -/
theorem tendsto_const_div_succ (c : ℝ) :
    Tendsto (fun t : ℕ => c / ((t : ℝ) + 1)) atTop (𝓝 0) := by
  have := (tendsto_const_div_atTop_nhds_zero_nat c).comp (tendsto_add_atTop_nat 1)
  refine this.congr fun t => ?_
  simp

/-- (L1) as a limit: `b ≡ 0` from some `t₀` gives `x_t → 0`. Source: doc §5. Kind: C -/
theorem cumul_tendsto_zero {x : ℕ → ℝ} {t₀ : ℕ}
    (h : ∀ t, t₀ ≤ t → x (t + 1) = cumulStep t (x t) 0) : Tendsto x atTop (𝓝 0) := by
  refine (tendsto_const_div_succ (x t₀ * (t₀ + 1))).congr' ?_
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  exact ⟨t₀, fun t ht => (cumul_zero_from h t ht).symm⟩

/-- (L1′) as a limit: `b ≡ 1` from some `t₀` gives `x_t → 1`. Source: doc §5. Kind: C -/
theorem cumul_tendsto_one {x : ℕ → ℝ} {t₀ : ℕ}
    (h : ∀ t, t₀ ≤ t → x (t + 1) = cumulStep t (x t) 1) : Tendsto x atTop (𝓝 1) := by
  have h1 : Tendsto (fun t : ℕ => 1 - (1 - x t₀) * (t₀ + 1) / ((t : ℝ) + 1)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_div_succ _)
  rw [sub_zero] at h1
  refine h1.congr' ?_
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  exact ⟨t₀, fun t ht => by linarith [cumul_one_from h t ht]⟩

/-- **(L2) one band step**: under the threshold rule at time `t` (`x_t < θ → b = 1`,
`θ ≤ x_t → b = 0`), `|x_t − θ| ≤ 1/(t+1)` implies `|x_{t+1} − θ| ≤ 1/(t+2)`, for `θ ∈ [0, 1]`.
Source: [[two-lesions-doc-2026-09-18]] §5 Proposition 5 proof ("`0` and `p̂` attract"), the
discrete mechanism made exact (mandate T8 L2)
Kind: P
Fidelity: exact
Hyps: none -/
theorem band_step {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {t : ℕ} {xt xt1 : ℝ}
    (hband : |xt - θ| ≤ 1 / ((t : ℝ) + 1))
    (hrule : (xt < θ → xt1 = cumulStep t xt 1) ∧ (θ ≤ xt → xt1 = cumulStep t xt 0)) :
    |xt1 - θ| ≤ 1 / ((t : ℝ) + 2) := by
  have hpos : (0 : ℝ) < t + 1 := by positivity
  have hpos2 : (0 : ℝ) < t + 2 := by positivity
  rw [abs_le] at hband ⊢
  obtain ⟨il, iu⟩ := hband
  have hle : 1 / ((t : ℝ) + 1) * ((t + 1) / (t + 2)) = 1 / ((t : ℝ) + 2) := by
    field_simp
  have hfrac : 0 ≤ ((t : ℝ) + 1) / (t + 2) := by positivity
  rcases le_or_gt θ xt with hge | hlt
  · rw [hrule.2 hge, cumulStep]
    have e : xt + (0 - xt) / (t + 2) - θ = (xt - θ) * ((t + 1) / (t + 2)) - θ / (t + 2) := by
      field_simp; ring
    rw [e]
    constructor
    · have : 0 ≤ (xt - θ) * (((t : ℝ) + 1) / (t + 2)) := mul_nonneg (by linarith) hfrac
      have : θ / ((t : ℝ) + 2) ≤ 1 / (t + 2) := by
        apply div_le_div_of_nonneg_right _ hpos2.le; linarith
      linarith
    · have : (xt - θ) * (((t : ℝ) + 1) / (t + 2)) ≤ 1 / ((t : ℝ) + 2) := by
        rw [← hle]; nlinarith
      have : 0 ≤ θ / ((t : ℝ) + 2) := by positivity
      linarith
  · rw [hrule.1 hlt, cumulStep]
    have e : xt + (1 - xt) / (t + 2) - θ = (xt - θ) * ((t + 1) / (t + 2)) + (1 - θ) / (t + 2) := by
      field_simp; ring
    rw [e]
    constructor
    · have : -(1 / ((t : ℝ) + 2)) ≤ (xt - θ) * ((t + 1) / (t + 2)) := by
        rw [← hle]; nlinarith
      have : 0 ≤ (1 - θ) / ((t : ℝ) + 2) := by
        apply div_nonneg _ hpos2.le; linarith
      linarith
    · have : (xt - θ) * (((t : ℝ) + 1) / (t + 2)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hfrac
      have : (1 - θ) / ((t : ℝ) + 2) ≤ 1 / (t + 2) := by
        apply div_le_div_of_nonneg_right _ hpos2.le; linarith
      linarith

/-- **(L2) the band**: under the threshold rule from time `T` on, with `|x_T − θ| ≤ 1/(T+1)`
and `θ ∈ [0, 1]`, `|x_t − θ| ≤ 1/(t+1)` for all `t ≥ T`.
Source: [[two-lesions-doc-2026-09-18]] §5 Proposition 5 proof; mandate T8 L2
Kind: P
Fidelity: exact
Hyps: none -/
theorem cumul_band {x : ℕ → ℝ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {T : ℕ}
    (hT : |x T - θ| ≤ 1 / (T + 1))
    (hrule : ∀ t, T ≤ t → (x t < θ → x (t + 1) = cumulStep t (x t) 1) ∧
      (θ ≤ x t → x (t + 1) = cumulStep t (x t) 0)) :
    ∀ t, T ≤ t → |x t - θ| ≤ 1 / (t + 1) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact hT
  | succ t ht ih =>
    have h := band_step hθ0 hθ1 ih (hrule t ht)
    push_cast
    rw [show ((t : ℝ) + 1 + 1) = (t : ℝ) + 2 by ring]
    exact h

/-- (L2) as a limit: under the band, `x_t → θ`. Source: doc §5. Kind: C -/
theorem cumul_tendsto_of_band {x : ℕ → ℝ} {θ : ℝ} {T : ℕ}
    (hband : ∀ t, T ≤ t → |x t - θ| ≤ 1 / (t + 1)) : Tendsto x atTop (𝓝 θ) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨max T N, fun t ht => ?_⟩
  rw [Real.dist_eq]
  have h1 := hband t (le_trans (le_max_left _ _) ht)
  have hNt : (N : ℝ) ≤ t := by exact_mod_cast le_trans (le_max_right T N) ht
  have hpos : (0 : ℝ) < t + 1 := by positivity
  calc |x t - θ| ≤ 1 / (t + 1) := h1
    _ < ε := by
      rw [div_lt_iff₀ hpos]
      have : 1 / ε < t + 1 := by linarith
      rw [div_lt_iff₀ hε] at this
      linarith

namespace DlParams

variable (P : DlParams ℝ)

/-- **The cumulative learner's trajectory** (doc §5, indexing disclosed): `x_{t+1} = x_t +
(b_t − x_t)/(t+2)` with `b_t ∈ β(x_t)`.
Source: [[two-lesions-doc-2026-09-18]] §5 ("The cumulative learner … `p̄_{t+1} = p̄_t + (b_t −
p̄_t)/(t+1)`"); mandate §3.8 (the shift)
Kind: D
Fidelity: variant: indexing shifted by one (`x₀` carried with weight one), disclosed -/
def IsCumulTraj (x : ℕ → ℝ) : Prop :=
  ∀ t, ∃ b ∈ P.bestResp (x t), x (t + 1) = cumulStep t (x t) b

/-- A cumulative trajectory stays in `[0, 1]`. Source: none: infrastructure. Kind: L -/
theorem cumul_mem_Icc {x : ℕ → ℝ} (htraj : P.IsCumulTraj x) (hx0 : 0 ≤ x 0 ∧ x 0 ≤ 1) (t : ℕ) :
    0 ≤ x t ∧ x t ≤ 1 := by
  induction t with
  | zero => exact hx0
  | succ t ih =>
    obtain ⟨b, hb, hstep⟩ := htraj t
    have hb0 := hb.2.2.1
    have hb1 := hb.2.2.2
    rw [hstep, cumulStep]
    have hpos : (0 : ℝ) < t + 2 := by positivity
    constructor
    · have : 0 ≤ (b - x t) / (t + 2) + x t := by
        rw [div_add' _ _ _ hpos.ne', div_nonneg_iff]; left; constructor <;> nlinarith
      linarith
    · have : (b - x t) / (t + 2) ≤ 1 - x t := by
        rw [div_le_iff₀ hpos]; nlinarith
      linarith

/-- The step with `b = 0` under a non-tie above the crossing set, from `bestResp = {0}`.
Source: none: infrastructure
Kind: L -/
theorem step_zero_of_gt {x : ℕ → ℝ} (htraj : P.IsCumulTraj x) (t : ℕ)
    (h : P.α < P.Delta (x t)) : x (t + 1) = cumulStep t (x t) 0 := by
  obtain ⟨b, hb, hstep⟩ := htraj t
  have hb0 : b = 0 := hb.2.1 h
  rw [hstep, hb0]

/-- The step with `b = 1` under a non-tie below `α`. Source: none: infrastructure. Kind: L -/
theorem step_one_of_lt {x : ℕ → ℝ} (htraj : P.IsCumulTraj x) (t : ℕ)
    (h : P.Delta (x t) < P.α) : x (t + 1) = cumulStep t (x t) 1 := by
  obtain ⟨b, hb, hstep⟩ := htraj t
  have hb1 : b = 1 := hb.1 h
  rw [hstep, hb1]

/-- **Proposition 5, strong grip** (no interior fixed point, `Q > 0` on `[0, 1]`): every
cumulative trajectory from `x₀ ∈ [0, 1]` converges to `0`. (H) is not needed: the regime
hypothesis already gives `Q(0) > 0` (audit r1).
Source: [[two-lesions-doc-2026-09-18]] §5 Proposition 5 ("if `δ > δ*`, then `p̄_t → 0` from every
initial policy")
Kind: P
Fidelity: exact (the regime as `Q > 0` on `[0, 1]`, equivalent under (H) to the unique fixed
point `0` by `prop3_unique_iff`)
Hyps: none (the regime hypothesis is the content; witness `prop5_strong_at_doc_deci`) -/
theorem prop5_strong (hQ : ∀ p ∈ Icc (0 : ℝ) 1, 0 < P.Q p) {x : ℕ → ℝ}
    (htraj : P.IsCumulTraj x) (hx0 : 0 ≤ x 0 ∧ x 0 ≤ 1) : Tendsto x atTop (𝓝 0) := by
  apply cumul_tendsto_zero (t₀ := 0)
  intro t _
  apply P.step_zero_of_gt htraj
  have hmem := P.cumul_mem_Icc htraj hx0 t
  exact (P.alpha_lt_Delta_iff _ hmem.1 hmem.2).mpr (hQ _ hmem)

/-- **Proposition 5, weak grip, the basin of `0`**: with fixed points `0 < p̌ < p̂ < 1` (`Q`'s
sign pattern), a trajectory from `x₀ < p̌` converges to `0`. (H) is not needed (audit r1).
Source: [[two-lesions-doc-2026-09-18]] §5 Proposition 5 ("`p̄_t → 0` when `p̄₀ < p̌`")
Kind: P
Fidelity: exact
Hyps: none (witness `prop5_weak_below_at_doc`) -/
theorem prop5_weak_below {p₁ p₂ : ℝ} (_h0 : 0 < p₁) (h12 : p₁ < p₂) (h1 : p₂ < 1)
    (hq1 : P.Q p₁ = 0) (hq2 : P.Q p₂ = 0) {x : ℕ → ℝ} (htraj : P.IsCumulTraj x)
    (hx0 : 0 ≤ x 0) (hx1 : x 0 < p₁) : Tendsto x atTop (𝓝 0) := by
  have hsign := P.Q_sign_pattern h12 hq1 hq2
  -- the trajectory stays below `p₁` and decreases
  have hbelow : ∀ t, 0 ≤ x t ∧ x t < p₁ := by
    intro t
    induction t with
    | zero => exact ⟨hx0, hx1⟩
    | succ t ih =>
      have hmem : 0 ≤ x t ∧ x t ≤ 1 := ⟨ih.1, by linarith⟩
      have hQ : 0 < P.Q (x t) := (hsign _).2.mpr (Or.inl ih.2)
      have hstep := P.step_zero_of_gt htraj t ((P.alpha_lt_Delta_iff _ hmem.1 hmem.2).mpr hQ)
      rw [hstep, cumulStep]
      have hpos : (0 : ℝ) < t + 2 := by positivity
      constructor
      · have : (0 - x t) / (t + 2) ≥ -x t := by
          rw [ge_iff_le, le_div_iff₀ hpos]; nlinarith
        linarith
      · have : (0 - x t) / (t + 2) ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
        linarith
  apply cumul_tendsto_zero (t₀ := 0)
  intro t _
  have hmem : 0 ≤ x t ∧ x t ≤ 1 := ⟨(hbelow t).1, by linarith [(hbelow t).2]⟩
  exact P.step_zero_of_gt htraj t
    ((P.alpha_lt_Delta_iff _ hmem.1 hmem.2).mpr ((hsign _).2.mpr (Or.inl (hbelow t).2)))

/-- The threshold rule at `p̂` while above `p̌`: a non-tying trajectory takes `b = 1` strictly
between the crossings and `b = 0` at or above `p̂`.
Source: none: infrastructure (the rule behind `prop5_weak_between`/`prop5_weak_above`)
Kind: L -/
theorem rule_between {p₁ p₂ : ℝ} (h12 : p₁ < p₂) (hq1 : P.Q p₁ = 0) (hq2 : P.Q p₂ = 0)
    {x : ℕ → ℝ} (htraj : P.IsCumulTraj x) (hnt : ∀ t, P.Delta (x t) ≠ P.α)
    (hmemI : ∀ t, 0 ≤ x t ∧ x t ≤ 1) (t : ℕ) (hgt : p₁ < x t) :
    (x t < p₂ → x (t + 1) = cumulStep t (x t) 1) ∧ (p₂ ≤ x t → x (t + 1) = cumulStep t (x t) 0) := by
  have hsign := P.Q_sign_pattern h12 hq1 hq2
  constructor
  · intro hlt
    apply P.step_one_of_lt htraj
    exact (P.Delta_lt_alpha_iff _ (hmemI t).1 (hmemI t).2).mpr ((hsign _).1.mpr ⟨hgt, hlt⟩)
  · intro hge
    rcases hge.lt_or_eq with hge | hge
    · apply P.step_zero_of_gt htraj
      exact (P.alpha_lt_Delta_iff _ (hmemI t).1 (hmemI t).2).mpr ((hsign _).2.mpr (Or.inr hge))
    · exfalso
      apply hnt t
      rw [P.Delta_eq_alpha_iff _ (hmemI t).1 (hmemI t).2, ← hge]; exact hq2

/-- **One step of the joint invariant** "`x_t > p̌` and `|x_t − p̂| ≤ 1/(t+1)`" under the gap
`p̌ + 1/3 < p̂`: the band step (L2) keeps the band, and the trajectory stays above `p̌` because
a rise cannot lower it and a drop from at or above `p̂` (only possible at `t ≥ 1`, or excluded
by `x_t < p̂`) is by the factor `(t+1)/(t+2) ≥ 2/3`, so `x_{t+1} ≥ 2p̂/3 > p̌`.
Source: none: infrastructure (the induction step shared by `prop5_weak_between` and
`prop5_weak_above`)
Kind: L -/
theorem between_step {p₁ p₂ : ℝ} (h0 : 0 < p₁) (h12 : p₁ < p₂) (h1 : p₂ < 1)
    (hq1 : P.Q p₁ = 0) (hq2 : P.Q p₂ = 0) (hgap : p₁ + 1/3 < p₂) {x : ℕ → ℝ}
    (htraj : P.IsCumulTraj x) (hnt : ∀ t, P.Delta (x t) ≠ P.α) (hmemI : ∀ t, 0 ≤ x t ∧ x t ≤ 1)
    {t : ℕ} (hcase : 1 ≤ t ∨ x t < p₂) (hgt : p₁ < x t) (hband : |x t - p₂| ≤ 1 / (t + 1)) :
    p₁ < x (t + 1) ∧ |x (t + 1) - p₂| ≤ 1 / ((t + 1 : ℕ) + 1) := by
  have hrule := P.rule_between h12 hq1 hq2 htraj hnt hmemI t hgt
  have hb : |x (t + 1) - p₂| ≤ 1 / ((t + 1 : ℕ) + 1) := by
    have h := band_step (by linarith : (0 : ℝ) ≤ p₂) h1.le hband hrule
    push_cast
    rw [show ((t : ℝ) + 1 + 1) = (t : ℝ) + 2 by ring]
    exact h
  refine ⟨?_, hb⟩
  rcases lt_or_ge (x t) p₂ with hlt | hge
  · rw [hrule.1 hlt, cumulStep]
    have hpos : (0 : ℝ) < t + 2 := by positivity
    have : 0 ≤ (1 - x t) / (t + 2) := div_nonneg (by linarith [(hmemI t).2]) hpos.le
    linarith
  · -- a drop from at or above `p₂`: `x_{t+1} = x_t (t+1)/(t+2) ≥ 2p₂/3` since `t ≥ 1` here
    rw [hrule.2 hge, cumulStep]
    have hpos : (0 : ℝ) < t + 2 := by positivity
    have ht1 : 1 ≤ t := by
      rcases hcase with h | h
      · exact h
      · exact absurd hge (not_le.mpr h)
    have ht1' : (1 : ℝ) ≤ t := by exact_mod_cast ht1
    have : x t + (0 - x t) / (t + 2) = x t * ((t + 1) / (t + 2)) := by field_simp; ring
    rw [this]
    have hfrac : (2 : ℝ) / 3 ≤ (t + 1) / (t + 2) := by
      rw [div_le_div_iff₀ (by norm_num) hpos]; linarith
    have : p₂ * (2 / 3) ≤ x t * ((t + 1) / (t + 2)) :=
      mul_le_mul hge hfrac (by norm_num) (by linarith [(hmemI t).1])
    linarith

/-- **Proposition 5, weak grip, the basin of `p̂` (gap `1/3`)**: with fixed points
`0 < p̌ < p̂ < 1`, a non-tying trajectory from `x₀ ∈ (p̌, p̂)` converges to `p̂` **provided
`p̌ + 1/3 < p̂`** — the joint invariant "`x_t > p̌` and `|x_t − p̂| ≤ 1/(t+1)`" (`between_step`)
holds from `t = 0`. (H) is not needed (audit r1).
Source: [[two-lesions-doc-2026-09-18]] §5 Proposition 5 ("`p̄_t → p̂` when `p̄₀ > p̌`"), corrected:
a gap condition is needed (`prop5_refuted_overshoot`)
Kind: P
Fidelity: weaker: the gap condition `p̂ − p̌ > 1/3` added (and necessary in some form: the doc's
clause is false without it)
Hyps: none beyond the regime, the gap and non-tying (all discharged at the doc's `δ = 1/100` by
`prop5_weak_between_at_doc`, the witness) -/
theorem prop5_weak_between {p₁ p₂ : ℝ} (h0 : 0 < p₁) (h12 : p₁ < p₂) (h1 : p₂ < 1)
    (hq1 : P.Q p₁ = 0) (hq2 : P.Q p₂ = 0) (hgap : p₁ + 1/3 < p₂) {x : ℕ → ℝ}
    (htraj : P.IsCumulTraj x) (hnt : ∀ t, P.Delta (x t) ≠ P.α) (hx0 : p₁ < x 0) (hx1 : x 0 < p₂) :
    Tendsto x atTop (𝓝 p₂) := by
  have hmemI : ∀ t, 0 ≤ x t ∧ x t ≤ 1 := P.cumul_mem_Icc htraj ⟨by linarith, by linarith⟩
  have hinv : ∀ t, p₁ < x t ∧ |x t - p₂| ≤ 1 / (t + 1) := by
    intro t
    induction t with
    | zero =>
      refine ⟨hx0, ?_⟩
      rw [abs_le]; constructor <;> norm_num <;> linarith [(hmemI 0).1]
    | succ t ih =>
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · exact P.between_step h0 h12 h1 hq1 hq2 hgap htraj hnt hmemI (Or.inr hx1) ih.1 ih.2
      · exact P.between_step h0 h12 h1 hq1 hq2 hgap htraj hnt hmemI (Or.inl ht) ih.1 ih.2
  exact cumul_tendsto_of_band (T := 0) fun t _ => (hinv t).2

/-- **Proposition 5, weak grip, from above `p̂` (gap `1/2`)**: with fixed points
`0 < p̌ < p̂ < 1` and `p̌ + 1/2 < p̂`, a non-tying trajectory from `x₀ ∈ (p̂, 1]` converges to
`p̂`: the first step halves `x₀` (so `x₁ = x₀/2 > p̂/2 > p̌`, because `p̂ > p̌ + 1/2 > 2p̌`, and
`|x₁ − p̂| ≤ 1/2`), after which the joint invariant of `between_step` runs from `t = 1`.
Source: [[two-lesions-doc-2026-09-18]] §5 Proposition 5 ("`p̄_t → p̂` when `p̄₀ > p̌`"), the
`p̄₀ > p̂` half, corrected by a gap condition
Kind: P
Fidelity: weaker: the gap condition `p̂ − p̌ > 1/2` added
Hyps: none beyond the regime, the gap and non-tying -/
theorem prop5_weak_above {p₁ p₂ : ℝ} (h0 : 0 < p₁) (h12 : p₁ < p₂) (h1 : p₂ < 1)
    (hq1 : P.Q p₁ = 0) (hq2 : P.Q p₂ = 0) (hgap : p₁ + 1/2 < p₂) {x : ℕ → ℝ}
    (htraj : P.IsCumulTraj x) (hnt : ∀ t, P.Delta (x t) ≠ P.α) (hx0 : p₂ < x 0) (hx1 : x 0 ≤ 1) :
    Tendsto x atTop (𝓝 p₂) := by
  have hgap' : p₁ + 1/3 < p₂ := by linarith
  have hmemI : ∀ t, 0 ≤ x t ∧ x t ≤ 1 := P.cumul_mem_Icc htraj ⟨by linarith, hx1⟩
  have hsign := P.Q_sign_pattern h12 hq1 hq2
  -- the first step halves `x₀`
  have hx1' : x 1 = x 0 / 2 := by
    have hstep := P.step_zero_of_gt htraj 0
      ((P.alpha_lt_Delta_iff _ (hmemI 0).1 (hmemI 0).2).mpr ((hsign _).2.mpr (Or.inr hx0)))
    rw [hstep, cumulStep]; push_cast; ring
  have hinv1 : p₁ < x 1 ∧ |x 1 - p₂| ≤ 1 / ((1 : ℕ) + 1) := by
    rw [hx1']
    constructor
    · linarith
    · push_cast
      rw [abs_le]; constructor <;> linarith
  have hinv : ∀ t, 1 ≤ t → p₁ < x t ∧ |x t - p₂| ≤ 1 / (t + 1) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact hinv1
    | succ t ht ih =>
      exact P.between_step h0 h12 h1 hq1 hq2 hgap' htraj hnt hmemI (Or.inl ht) ih.1 ih.2
  exact cumul_tendsto_of_band (T := 1) fun t ht => (hinv t ht).2

/-- **Proposition 5 refuted as stated: overshoot**. At the doc's parameters with
`δ = 139/5000` (just below `δ*`, regime of three fixed points `0 < p̌ < p̂ < 1`), the
cumulative trajectory from `x₀ = 33/50 ∈ (p̌, p̂)` is non-tying, overshoots to `x₁ = 83/100 > p̂`,
drops to `x₂ = 83/150 < p̌`, and converges to `0` — not to `p̂`. The doc's "`p̄_t → p̂` when
`p̄₀ > p̌`" fails because its Euler-scheme heuristic ignores the early steps' size.
Source: [[two-lesions-doc-2026-09-18]] §5 Proposition 5 ("`p̄_t → p̂` when `p̄₀ > p̌`"), refuted
Kind: N+ (a refutation witness, exact)
Fidelity: exact -/
theorem prop5_refuted_overshoot :
    let P := docP (139/5000 : ℝ) (by norm_num) (by norm_num)
    ∃ p₁ p₂ : ℝ, 0 < p₁ ∧ p₁ < p₂ ∧ p₂ < 1 ∧ P.fixedPts = {0, p₁, p₂} ∧
      ∃ x : ℕ → ℝ, P.IsCumulTraj x ∧ (∀ t, P.Delta (x t) ≠ P.α) ∧ p₁ < x 0 ∧ x 0 < p₂ ∧
        Tendsto x atTop (𝓝 0) := by
  intro P
  have hH := docP_hypH (139/5000 : ℝ) (by norm_num) (by norm_num)
  have hreg : 0 < discrim P.qA P.qB P.qE ∧ 0 < -P.qB / (2 * P.qA) ∧ -P.qB / (2 * P.qA) < 1 := by
    refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [P, discrim, qA, qB, qE, kappa, kcC, docP]
      norm_num
  obtain ⟨p₁, p₂, h0, h12, h1, hset⟩ := (P.prop3_three_iff hH).mpr hreg
  have hmem : ∀ p ∈ P.fixedPts, p = 0 ∨ (0 < p ∧ p < 1 ∧ P.Q p = 0) := by
    intro p hp
    rw [P.prop3_fixedPoints_eq hH] at hp
    simpa using hp
  have hq1 : P.Q p₁ = 0 := by
    rcases hmem p₁ (by rw [hset]; simp) with h | h
    · exact absurd h h0.ne'
    · exact h.2.2
  have hq2 : P.Q p₂ = 0 := by
    rcases hmem p₂ (by rw [hset]; simp) with h | h
    · exact absurd h (by linarith)
    · exact h.2.2
  have hsign := P.Q_sign_pattern h12 hq1 hq2
  -- the signs of `Q` at the three points
  have e0 : P.Q (33/50) < 0 := by
    simp only [P, Q, qA, qB, qE, kappa, kcC, docP]; norm_num
  have e1 : 0 < P.Q (83/100) := by
    simp only [P, Q, qA, qB, qE, kappa, kcC, docP]; norm_num
  have e2 : 0 < P.Q (83/150) := by
    simp only [P, Q, qA, qB, qE, kappa, kcC, docP]; norm_num
  have hb0 := (hsign _).1.mp e0   -- p₁ < 33/50 < p₂
  have hb2 : 83/150 < p₁ := by
    rcases (hsign _).2.mp e2 with h | h
    · exact h
    · linarith [hb0.2]
  -- the explicit trajectory
  let x : ℕ → ℝ := fun t => match t with
    | 0 => 33/50
    | 1 => 83/100
    | t + 2 => 83 / (50 * ((t : ℝ) + 3))
  have hx0 : x 0 = 33/50 := rfl
  have hx1 : x 1 = 83/100 := rfl
  have hx2 : ∀ t, x (t + 2) = 83 / (50 * ((t : ℝ) + 3)) := fun t => rfl
  have hxpos : ∀ t, 0 < x (t + 2) ∧ x (t + 2) ≤ 83/150 := by
    intro t
    rw [hx2]
    have : (3 : ℝ) ≤ t + 3 := by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
    constructor
    · positivity
    · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  refine ⟨p₁, p₂, h0, h12, h1, hset, x, ?_, ?_, by rw [hx0]; exact hb0.1, by rw [hx0]; exact hb0.2,
    ?_⟩
  · -- the trajectory follows the recursion
    intro t
    match t with
    | 0 =>
      refine ⟨1, ?_, ?_⟩
      · have hlt : P.Delta (x 0) < P.α := by
          rw [hx0, P.Delta_lt_alpha_iff _ (by norm_num) (by norm_num)]; exact e0
        exact ⟨fun _ => rfl, fun h => absurd h (not_lt.mpr hlt.le), zero_le_one, le_rfl⟩
      · rw [hx1, hx0, cumulStep]; norm_num
    | 1 =>
      refine ⟨0, ?_, ?_⟩
      · have hgt : P.α < P.Delta (x 1) := by
          rw [hx1, P.alpha_lt_Delta_iff _ (by norm_num) (by norm_num)]; exact e1
        exact ⟨fun h => absurd h (not_lt.mpr hgt.le), fun _ => rfl, le_rfl, zero_le_one⟩
      · rw [hx2 0, hx1, cumulStep]; norm_num
    | t + 2 =>
      refine ⟨0, ?_, ?_⟩
      · have hmem := hxpos t
        have hQ : 0 < P.Q (x (t + 2)) :=
          (hsign _).2.mpr (Or.inl (by linarith [hmem.2]))
        have hgt : P.α < P.Delta (x (t + 2)) :=
          (P.alpha_lt_Delta_iff _ hmem.1.le (by linarith [hmem.2])).mpr hQ
        exact ⟨fun h => absurd h (not_lt.mpr hgt.le), fun _ => rfl, le_rfl, zero_le_one⟩
      · rw [hx2, hx2, cumulStep]
        push_cast
        have h3 : ((t : ℝ) + 3) ≠ 0 := by positivity
        have h4 : ((t : ℝ) + 2 + 2) ≠ 0 := by positivity
        have h4' : ((t : ℝ) + 1 + 3) ≠ 0 := by positivity
        field_simp
        ring
  · -- never ties
    intro t
    match t with
    | 0 =>
      rw [hx0, Ne, P.Delta_eq_alpha_iff _ (by norm_num) (by norm_num)]; exact e0.ne
    | 1 =>
      rw [hx1, Ne, P.Delta_eq_alpha_iff _ (by norm_num) (by norm_num)]; exact e1.ne'
    | t + 2 =>
      have hmem := hxpos t
      rw [Ne, P.Delta_eq_alpha_iff _ hmem.1.le (by linarith [hmem.2])]
      exact ((hsign _).2.mpr (Or.inl (by linarith [hmem.2]))).ne'
  · -- converges to `0`
    have hlim : Tendsto (fun t : ℕ => 83 / (50 * ((t : ℝ) + 1))) atTop (𝓝 0) := by
      have := tendsto_const_div_succ (83/50 : ℝ)
      refine this.congr fun t => ?_
      field_simp
    refine hlim.congr' ?_
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    refine ⟨2, fun t ht => ?_⟩
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
    rw [hx2]
    push_cast
    ring_nf

/-- **Outside (H), the cumulative learner smokes** (`sessP`, dp-core-2-009(d)): `Q(0) > 0 > Q(1)`,
so there is a crossing `p* ∈ (0, 1)` (`Δ(p*) = α`), the only one in `(0, 1)`, bracketed in
`(0.0201, 0.0202)`, with `Δ < α` on `(p*, 1]`; every cumulative trajectory from `x₀ ∈ (p*, 1]`
has `b ≡ 1` and converges to `1`.
Source: [[iv-design-draw-as-instrument]] §5 ("the only interior crossing is `p* = 0.0201`, and
every learner from a start above it converges to `p = 1`")
Kind: P
Fidelity: exact (bracketing interval, rule 4; the crossing and its uniqueness in the statement
since audit r1)
Hyps: none -/
theorem prop5_outsideH_smokes :
    ∃ pStar : ℝ, 201/10000 < pStar ∧ pStar < 202/10000 ∧
      (sessP : DlParams ℝ).Delta pStar = (sessP : DlParams ℝ).α ∧
      (∀ p, 0 < p → p < 1 → (sessP : DlParams ℝ).Delta p = (sessP : DlParams ℝ).α → p = pStar) ∧
      (∀ p, pStar < p → p ≤ 1 → (sessP : DlParams ℝ).Delta p < (sessP : DlParams ℝ).α) ∧
      (∀ x : ℕ → ℝ, (sessP : DlParams ℝ).IsCumulTraj x → pStar < x 0 → x 0 ≤ 1 →
        Tendsto x atTop (𝓝 1)) := by
  set P : DlParams ℝ := sessP with hP
  have hA := P.qA_pos
  have hQ0 : 0 < P.Q 0 := by simp only [P, Q, qA, qB, qE, kappa, kcC, sessP]; norm_num
  have hQ1 : P.Q 1 < 0 := by simp only [P, Q, qA, qB, qE, kappa, kcC, sessP]; norm_num
  -- the discriminant is positive (`Q` takes a negative value)
  have hd : 0 < discrim P.qA P.qB P.qE := by
    by_contra hle
    have hle' := not_lt.mp hle
    have : 4 * P.qA * P.Q 1 = (2 * P.qA * 1 + P.qB) ^ 2 - discrim P.qA P.qB P.qE := by
      unfold Q discrim; ring
    nlinarith [sq_nonneg (2 * P.qA * 1 + P.qB)]
  set s := Real.sqrt (discrim P.qA P.qB P.qE) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hd
  have hss : discrim P.qA P.qB P.qE = s * s := (Real.mul_self_sqrt hd.le).symm
  set r₁ := (-P.qB - s) / (2 * P.qA) with hr₁
  set r₂ := (-P.qB + s) / (2 * P.qA) with hr₂
  have hroot : ∀ p, P.Q p = 0 ↔ p = r₂ ∨ p = r₁ := by
    intro p; rw [P.Q_eq_mul_self]; exact quadratic_eq_zero_iff hA.ne' hss p
  have hq1 : P.Q r₁ = 0 := (hroot _).mpr (Or.inr rfl)
  have hq2 : P.Q r₂ = 0 := (hroot _).mpr (Or.inl rfl)
  have h12 : r₁ < r₂ := by
    rw [hr₁, hr₂]; apply div_lt_div_of_pos_right _ (by linarith); linarith
  have hsign := P.Q_sign_pattern h12 hq1 hq2
  -- `0 < r₁` and `1 ∈ (r₁, r₂)`
  have h1in := (hsign 1).1.mp hQ1
  have h0out := (hsign 0).2.mp hQ0
  have hr₁pos : 0 < r₁ := by
    rcases h0out with h | h
    · exact h
    · linarith [h1in.2]
  -- the brackets
  have e1 : 0 < P.Q (201/10000) := by simp only [P, Q, qA, qB, qE, kappa, kcC, sessP]; norm_num
  have e2 : P.Q (202/10000) < 0 := by simp only [P, Q, qA, qB, qE, kappa, kcC, sessP]; norm_num
  have hb1 : 201/10000 < r₁ := by
    rcases (hsign _).2.mp e1 with h | h
    · exact h
    · linarith [((hsign _).1.mp e2).2]
  have hb2 : r₁ < 202/10000 := ((hsign _).1.mp e2).1
  refine ⟨r₁, hb1, hb2, ?_, fun p hp0 hp1 htie => ?_, fun p hp hp1 => ?_,
    fun x htraj hx0 hx1 => ?_⟩
  · exact (P.Delta_eq_alpha_iff _ hr₁pos.le (by linarith)).mpr hq1
  · rw [P.Delta_eq_alpha_iff _ hp0.le hp1.le, hroot] at htie
    rcases htie with h | h
    · exact absurd h (by linarith [h1in.2])
    · exact h
  · rw [P.Delta_lt_alpha_iff _ (by linarith) hp1]
    exact (hsign _).1.mpr ⟨hp, lt_of_le_of_lt hp1 h1in.2⟩
  · -- `b ≡ 1`: the trajectory increases and stays above `r₁`
    have hinv : ∀ t, r₁ < x t ∧ x t ≤ 1 := by
      intro t
      induction t with
      | zero => exact ⟨hx0, hx1⟩
      | succ t ih =>
        have hlt : P.Delta (x t) < P.α := by
          rw [P.Delta_lt_alpha_iff _ (by linarith [ih.1]) ih.2]
          exact (hsign _).1.mpr ⟨ih.1, lt_of_le_of_lt ih.2 h1in.2⟩
        rw [P.step_one_of_lt htraj t hlt, cumulStep]
        have hpos : (0 : ℝ) < t + 2 := by positivity
        constructor
        · have : 0 ≤ (1 - x t) / (t + 2) := div_nonneg (by linarith [ih.2]) hpos.le
          linarith [ih.1]
        · have : (1 - x t) / (t + 2) ≤ 1 - x t := by
            rw [div_le_iff₀ hpos]; nlinarith [ih.2]
          linarith
    apply cumul_tendsto_one (t₀ := 0)
    intro t _
    apply P.step_one_of_lt htraj
    rw [P.Delta_lt_alpha_iff _ (by linarith [(hinv t).1]) (hinv t).2]
    exact (hsign _).1.mpr ⟨(hinv t).1, lt_of_le_of_lt (hinv t).2 h1in.2⟩

/-! ## Discharging the no-tie hypothesis at the doc's numbers -/

/-- `√105835` is irrational (`105835` is not a perfect square: `325² < 105835 < 326²`).
Source: none: infrastructure
Kind: L -/
theorem irrational_sqrt_105835 : Irrational (Real.sqrt 105835) := by
  have hsq : Real.sqrt 105835 ^ 2 = ((105835 : ℤ) : ℝ) := by
    rw [Real.sq_sqrt (by norm_num)]; norm_num
  refine irrational_nrt_of_notint_nrt 2 105835 hsq ?_ (by norm_num)
  rintro ⟨y, hy⟩
  have hlo : (325 : ℝ) < y := by rw [← hy]; exact (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hhi : (y : ℝ) < 326 := by rw [← hy]; exact (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have h1 : (325 : ℤ) < y := by exact_mod_cast hlo
  have h2 : y < (326 : ℤ) := by exact_mod_cast hhi
  omega

/-- **No rational label ties at the doc's `δ = 1/100`**: a tie `Δ(p) = α` at `p ∈ [0, 1]` puts
`p` in `fixedPts = {0, p̌, p̂}`; `0` is not a tie (`Δ(0) > α`), and `p̌, p̂` are irrational
(surds in `√105835`).
Source: mandate §3.8 ("`p̌, p̂ ∉ ℚ` at `δ = 1/100`")
Kind: P
Fidelity: exact
Hyps: none -/
theorem rat_noTie_at_doc {p : ℝ} (hrat : ∃ q : ℚ, p = q) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    docCenti.Delta p ≠ docCenti.α := by
  have hH := docP_hypH (1/100 : ℝ) (by norm_num) (by norm_num)
  obtain ⟨hr0, hr12, hr1, hset⟩ := prop3_three_at_doc_centi
  intro htie
  have hfp : p ∈ docCenti.fixedPts := by
    rw [docCenti.prop3_fixedPoints_eq hH]
    rcases h0.lt_or_eq with h0' | h0'
    · rcases h1.lt_or_eq with h1' | h1'
      · right
        exact ⟨h0', h1', (docCenti.Delta_eq_alpha_iff _ h0 h1).mp htie⟩
      · exfalso
        rw [h1'] at htie
        exact (docCenti.alpha_lt_Delta_one hH).ne' htie
    · left; exact h0'.symm
  rw [hset] at hfp
  obtain ⟨q, hq⟩ := hrat
  have hirr := irrational_sqrt_105835
  simp only [mem_insert_iff, mem_singleton_iff] at hfp
  rcases hfp with h | h | h
  · -- `p = 0` is not a tie: `Δ(0) > α`
    rw [h] at htie
    exact (docCenti.alpha_lt_Delta_zero hH).ne' htie
  · -- `p = p̌`, irrational
    apply hirr
    rw [hq] at h
    refine ⟨(23167/41334 - q) * 20667 / 25, ?_⟩
    push_cast
    linarith
  · apply hirr
    rw [hq] at h
    refine ⟨(q - 23167/41334) * 20667 / 25, ?_⟩
    push_cast
    linarith

/-- **The no-tie hypothesis is discharged for every rational-start trajectory at the doc's
`δ = 1/100`**: for every cumulative trajectory `x` of `docCenti` from a rational `x₀ ∈ [0, 1]`,
every `x_t` is rational and `Δ(x_t) ≠ α` — one induction alternating "rational ⇒ no tie
(`rat_noTie_at_doc`) ⇒ the best response is `{0}` or `{1}` ⇒ the next value is rational". No
restriction on the selection rule is assumed (audit r1 B1: the earlier form assumed `b ∈ {0, 1}`,
which is what this proves).
Source: mandate §3.8 ("discharge it at the doc's numbers by irrationality")
Kind: P
Fidelity: exact
Hyps: none -/
theorem noTie_of_rat_at_doc {x : ℕ → ℝ} (htraj : docCenti.IsCumulTraj x)
    (hrat : ∃ q : ℚ, x 0 = q) (hx0 : 0 ≤ x 0 ∧ x 0 ≤ 1) :
    ∀ t, (∃ q : ℚ, x t = q) ∧ docCenti.Delta (x t) ≠ docCenti.α := by
  have hmem := docCenti.cumul_mem_Icc htraj hx0
  have hratt : ∀ t, ∃ q : ℚ, x t = q := by
    intro t
    induction t with
    | zero => exact hrat
    | succ t ih =>
      obtain ⟨q, hq⟩ := ih
      have hne := rat_noTie_at_doc ⟨q, hq⟩ (hmem t).1 (hmem t).2
      obtain ⟨b, hb, hstep⟩ := htraj t
      have hb01 : b = 0 ∨ b = 1 := by
        rcases lt_or_gt_of_ne hne with h | h
        · exact Or.inr (hb.1 h)
        · exact Or.inl (hb.2.1 h)
      rw [hstep, cumulStep, hq]
      rcases hb01 with rfl | rfl
      · exact ⟨q + (0 - q) / (t + 2), by push_cast; ring⟩
      · exact ⟨q + (1 - q) / (t + 2), by push_cast; ring⟩
  intro t
  exact ⟨hratt t, rat_noTie_at_doc (hratt t) (hmem t).1 (hmem t).2⟩

/-- **Proposition 5's basin of `p̂` at the doc's `δ = 1/100`, hypothesis-free** (the witness for
`prop5_weak_between`'s full package): every cumulative trajectory of `docCenti` from a rational
start in `(p̌, p̂)` converges to `p̂ = 23167/41334 + 25√105835/20667`. The roots come from
`prop3_three_at_doc_centi`, the gap `p̂ − p̌ = 50√105835/20667 > 1/3` from `sqrt_105835_bounds`,
the no-tie from `noTie_of_rat_at_doc`.
Source: [[two-lesions-doc-2026-09-18]] §5 Proposition 5 and its `δ = 1/100` runs ("reaches
`0.954 = p̂`")
Kind: N+ (a non-degenerate instance: every rational start in `(p̌, p̂)`, e.g. `½`)
Fidelity: exact
Hyps: none -/
theorem prop5_weak_between_at_doc {x : ℕ → ℝ} (htraj : docCenti.IsCumulTraj x)
    (hrat : ∃ q : ℚ, x 0 = q)
    (hx0 : 23167/41334 - 25 * Real.sqrt 105835 / 20667 < x 0)
    (hx1 : x 0 < 23167/41334 + 25 * Real.sqrt 105835 / 20667) :
    Tendsto x atTop (𝓝 (23167/41334 + 25 * Real.sqrt 105835 / 20667)) := by
  obtain ⟨hr0, hr12, hr1, hset⟩ := prop3_three_at_doc_centi
  have hH := docP_hypH (1/100 : ℝ) (by norm_num) (by norm_num)
  have hmem : ∀ p ∈ docCenti.fixedPts, p = 0 ∨ (0 < p ∧ p < 1 ∧ docCenti.Q p = 0) := by
    intro p hp
    rw [docCenti.prop3_fixedPoints_eq hH] at hp
    simpa using hp
  have hq1 : docCenti.Q (23167/41334 - 25 * Real.sqrt 105835 / 20667) = 0 := by
    rcases hmem (23167/41334 - 25 * Real.sqrt 105835 / 20667) (by rw [hset]; simp) with h | h
    · exact absurd h hr0.ne'
    · exact h.2.2
  have hq2 : docCenti.Q (23167/41334 + 25 * Real.sqrt 105835 / 20667) = 0 := by
    rcases hmem (23167/41334 + 25 * Real.sqrt 105835 / 20667) (by rw [hset]; simp) with h | h
    · exact absurd h (by linarith)
    · exact h.2.2
  have hgap : 23167/41334 - 25 * Real.sqrt 105835 / 20667 + 1/3 <
      23167/41334 + 25 * Real.sqrt 105835 / 20667 := by
    have := sqrt_105835_bounds.1; linarith
  have hnt := noTie_of_rat_at_doc htraj hrat ⟨by linarith, by linarith⟩
  exact docCenti.prop5_weak_between hr0 hr12 hr1 hq1 hq2 hgap htraj (fun t => (hnt t).2) hx0 hx1

end DlParams

end Cleanroom.Decision.DpTwoLesions
