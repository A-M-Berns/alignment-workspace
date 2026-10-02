import Cleanroom.Found.LiAsympCalc.Defs
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
# D. The ramp and the doubly-soft gate

Target D of [[li-asymp-calc-mandate]].

* D1: the corpus's ramp `Ind_δ(x > t)` **is** FAF's `ctsInd δ x t`; `softInd δ (x - t)` (the
  earlier Lean's `max 0 (min 1 ((x-t)/δ))`) equals it because the clamps commute. For `0 < δ`:
  boundary one-sidedness (`ctsInd δ t t = 0`; `= 0 ↔ x ≤ y`; `0 < · ↔ y < x`; `= 1 ↔ δ ≤ x - y`),
  range `[0,1]`, joint continuity, and the **sandwich** between the sharp indicators at
  thresholds `t + δ` and `t`.
* D2: the doubly-soft weight `dsWeight` is jointly continuous, `[0,1]`-valued, and its support
  forces both inequalities. Its feature form `dsFeature` denotes it in one market
  (`dsFeature_denote`); the generability certificate is in `Feature.lean` (the only file that
  imports `Construction.*`).
* D3: **a hard indicator of a price is not an expressible feature**: `EF.denote` is continuous
  in the product topology on `History`, and along the path that varies one price the indicator
  jumps. About trade weights, not LUVs.
-/

namespace Cleanroom.Found.LiAsympCalc

open LogicalInduction Filter Topology

/-! ### D1. The ramp is `ctsInd` -/

/-- The earlier Lean's `softInd δ (x - t) = max 0 (min 1 ((x - t)/δ))` is FAF's `ctsInd δ x t`:
the two clamps commute.
Source: lean-deference-2-017; root-fa-004
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ctsInd_eq_softInd (δ : ℚ) (x t : ℝ) :
    ctsInd δ x t = max 0 (min 1 ((x - t) / (δ : ℝ))) := by
  unfold ctsInd
  rw [max_min_distrib_left, max_eq_right zero_le_one]

/-- Boundary one-sidedness: the ramp is `0` at its own threshold, for every width.
Source: root-fa-004; [[faithful-acceleration]] §5
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ctsInd_self (δ : ℚ) (t : ℝ) : ctsInd δ t t = 0 := by
  simp [ctsInd]

/-- `0 ≤ ctsInd δ x y`.
Source: FAF `ctsInd_mem_Icc`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ctsInd_nonneg (δ : ℚ) (x y : ℝ) : 0 ≤ ctsInd δ x y := (ctsInd_mem_Icc δ x y).1

/-- `ctsInd δ x y ≤ 1`.
Source: FAF `ctsInd_mem_Icc`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ctsInd_le_one (δ : ℚ) (x y : ℝ) : ctsInd δ x y ≤ 1 := (ctsInd_mem_Icc δ x y).2

/-- For a positive width, the ramp vanishes exactly at or below the threshold. (FAF's
`ctsInd_eq_zero_of_le` sits in `Construction/Quotation/DeferralFibre.lean`; the one-liner is
re-proved here so that `Ramp.lean` imports no `Construction.*` module.)
Source: root-fa-004; [[faithful-acceleration]] §5
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ctsInd_eq_zero_iff {δ : ℚ} (hδ : 0 < δ) (x y : ℝ) : ctsInd δ x y = 0 ↔ x ≤ y := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold ctsInd
  constructor
  · intro h
    by_contra hxy
    rw [not_le] at hxy
    have hpos : 0 < (x - y) / (δ : ℝ) := div_pos (by linarith) hδR
    have h1 : 0 < min 1 (max 0 ((x - y) / (δ : ℝ))) :=
      lt_min zero_lt_one (lt_max_of_lt_right hpos)
    linarith
  · intro hxy
    have hle : (x - y) / (δ : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδR.le
    rw [max_eq_left hle, min_eq_right zero_le_one]

/-- For a positive width, the ramp is positive exactly strictly above the threshold.
Source: root-fa-004; [[faithful-acceleration]] §5
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ctsInd_pos_iff {δ : ℚ} (hδ : 0 < δ) (x y : ℝ) : 0 < ctsInd δ x y ↔ y < x := by
  constructor
  · intro h
    by_contra hxy
    rw [(ctsInd_eq_zero_iff hδ x y).2 (not_lt.1 hxy)] at h
    exact lt_irrefl _ h
  · intro h
    refine lt_of_le_of_ne (ctsInd_nonneg δ x y) (fun heq => ?_)
    exact not_le.2 h ((ctsInd_eq_zero_iff hδ x y).1 heq.symm)

/-- For a positive width, the ramp is `1` exactly when the gap is at least the width.
Source: FAF `ctsInd_eq_one_of_le_sub` (one direction); root-fa-004
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ctsInd_eq_one_iff {δ : ℚ} (hδ : 0 < δ) (x y : ℝ) :
    ctsInd δ x y = 1 ↔ (δ : ℝ) ≤ x - y := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  constructor
  · intro h
    unfold ctsInd at h
    by_contra hlt
    rw [not_le] at hlt
    have hr : (x - y) / (δ : ℝ) < 1 := (div_lt_one hδR).2 hlt
    have : min 1 (max 0 ((x - y) / (δ : ℝ))) < 1 :=
      lt_of_le_of_lt (min_le_right _ _) (max_lt zero_lt_one hr)
    linarith
  · exact ctsInd_eq_one_of_le_sub δ x y hδ

/-- The ramp is jointly continuous in `(x, y)` (a fixed positive or negative width; at `δ = 0`
the quotient is `0` and continuity is trivial too).
Source: [[faithful-acceleration]] §9; root-fa-004
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem continuous_ctsInd (δ : ℚ) : Continuous (fun p : ℝ × ℝ => ctsInd δ p.1 p.2) := by
  unfold ctsInd
  fun_prop

/-- **Sandwich**: for `0 < δ`, `1[t + δ < x] ≤ ctsInd δ x t ≤ 1[t < x]`. This is what "the ramp
family and the sharp family agree under full quantification" means for monotone uses; the
family-level equivalence is E1 (`Compactness.lean`).
Source: lean-deference-2-017; root-fa-004
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ctsInd_sandwich {δ : ℚ} (hδ : 0 < δ) (x t : ℝ) :
    (if t + (δ : ℝ) < x then (1 : ℝ) else 0) ≤ ctsInd δ x t ∧
      ctsInd δ x t ≤ (if t < x then (1 : ℝ) else 0) := by
  constructor
  · split_ifs with h
    · exact (ctsInd_eq_one_of_le_sub δ x t hδ (by linarith)).ge
    · exact ctsInd_nonneg δ x t
  · split_ifs with h
    · exact ctsInd_le_one δ x t
    · exact ((ctsInd_eq_zero_iff hδ x t).2 (not_lt.1 h)).le

/-! ### D2. The doubly-soft weight -/

/-- `0 ≤ dsWeight t ε δ a p`.
Source: `lean-deference` `FaithfulAcceleration.lean:169`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem dsWeight_nonneg (t ε : ℝ) (δ : ℚ) (a p : ℝ) : 0 ≤ dsWeight t ε δ a p :=
  mul_nonneg (ctsInd_nonneg _ _ _) (ctsInd_nonneg _ _ _)

/-- `dsWeight t ε δ a p ≤ 1`.
Source: `lean-deference` `FaithfulAcceleration.lean:169`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem dsWeight_le_one (t ε : ℝ) (δ : ℚ) (a p : ℝ) : dsWeight t ε δ a p ≤ 1 :=
  mul_le_one₀ (ctsInd_le_one _ _ _) (ctsInd_nonneg _ _ _) (ctsInd_le_one _ _ _)

/-- The doubly-soft weight is jointly continuous in `(a, p)`.
Source: `lean-deference` `FaithfulAcceleration.lean:169–203` (`dsWeight_continuous`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem continuous_dsWeight (t ε : ℝ) (δ : ℚ) :
    Continuous (fun q : ℝ × ℝ => dsWeight t ε δ q.1 q.2) := by
  unfold dsWeight ctsInd
  fun_prop

/-- **Support forces both inequalities** (D2): `0 < dsWeight t ε δ a p → t < a ∧ p < t - ε`,
for a positive width. The two facts the earlier Lean assumed as `hone`/`hmis` are theorems
about the construction (two applications of `ctsInd_pos_iff`; graded `L` for that reason).
Source: `lean-deference` `FaithfulAcceleration.lean:169–203`; [[AUDIT]] §3.2
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem dsWeight_pos_imp {t ε : ℝ} {δ : ℚ} (hδ : 0 < δ) {a p : ℝ}
    (h : 0 < dsWeight t ε δ a p) : t < a ∧ p < t - ε := by
  unfold dsWeight at h
  have h1 : 0 < ctsInd δ a t := by
    rcases (ctsInd_nonneg δ a t).lt_or_eq with h1 | h1
    · exact h1
    · rw [← h1, zero_mul] at h
      exact absurd h (lt_irrefl 0)
  have h2 : 0 < ctsInd δ (t - ε) p := by
    rcases (ctsInd_nonneg δ (t - ε) p).lt_or_eq with h2 | h2
    · exact h2
    · rw [← h2, mul_zero] at h
      exact absurd h (lt_irrefl 0)
  exact ⟨(ctsInd_pos_iff hδ a t).1 h1, (ctsInd_pos_iff hδ (t - ε) p).1 h2⟩

/-- The doubly-soft weight is fully on once both gaps are at least the width.
Source: [[fa-positive-results-corrected-v2]] §5.5
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem dsWeight_eq_one {t ε : ℝ} {δ : ℚ} (hδ : 0 < δ) {a p : ℝ}
    (ha : (δ : ℝ) ≤ a - t) (hp : (δ : ℝ) ≤ (t - ε) - p) : dsWeight t ε δ a p = 1 := by
  unfold dsWeight
  rw [ctsInd_eq_one_of_le_sub δ a t hδ ha, ctsInd_eq_one_of_le_sub δ (t - ε) p hδ hp, mul_one]

/-- `rampFeature δ x y` denotes `ctsInd δ (x.denote P) (y.denote P)` for a positive width
(mirrors FAF's `ctsIndFeature_denote`).
Source: FAF `ctsIndFeature_denote` (re-proved: `Construction.*` is not imported here)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem rampFeature_denote {δ : ℚ} (hδ : 0 < δ) (x y : EF) (P : History) :
    (rampFeature δ x y).denote P = ctsInd δ (x.denote P) (y.denote P) := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  rw [rampFeature, clip01_denote]
  simp only [EF.denote_mul, EF.denote_add, EF.denote_const, Pi.mul_apply, Pi.add_apply,
    Rat.cast_neg, Rat.cast_one, Rat.cast_div]
  rw [max_min_distrib_left, max_eq_right zero_le_one]
  unfold ctsInd
  congr 2
  field_simp
  ring

/-- **`dsFeature` denotes `dsWeight` in one market** (D2, legality half): the feature of the
day-`n` prices of `φ` and `ψ` in history `P` evaluates to `dsWeight t ε δ (P n φ) (P n ψ)`.
Source: [[faithful-acceleration]] §5, §9; [[AUDIT]] §3.2
Kind: L
Fidelity: exact (one-market form; the cross-market quote is `li-quote-lane`'s)
Hyps: (a) none -/
theorem dsFeature_denote (φ ψ : Sentence) {t ε δ : ℚ} (hδ : 0 < δ) (n : ℕ) (P : History) :
    (dsFeature φ ψ t ε δ n).denote P = dsWeight t ε δ (P n φ) (P n ψ) := by
  rw [dsFeature, EF.denote_mul, Pi.mul_apply, rampFeature_denote hδ, rampFeature_denote hδ]
  simp only [EF.denote_price, EF.denote_const, dsWeight, Rat.cast_sub]

/-- `dsFeature` is `[0,1]`-valued at every market (the range half of a `DivergentWeighting`).
Source: [[li-asymp-calc-mandate]] D2
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem dsFeature_mem_Icc (φ ψ : Sentence) {t ε δ : ℚ} (hδ : 0 < δ) (n : ℕ) (P : History) :
    0 ≤ (dsFeature φ ψ t ε δ n).denote P ∧ (dsFeature φ ψ t ε δ n).denote P ≤ 1 := by
  rw [dsFeature_denote φ ψ hδ]
  exact ⟨dsWeight_nonneg _ _ _ _ _, dsWeight_le_one _ _ _ _ _⟩

/-! ### D3. A hard indicator of a price is not an expressible feature -/

/-- The one-price path `s ↦ V[n ↦ V n[φ ↦ s]]` through `History` is continuous.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem continuous_pricePath (V : History) (n : ℕ) (φ : Sentence) :
    Continuous (fun s : ℝ => Function.update V n (Function.update (V n) φ s)) :=
  continuous_const.update n (continuous_const.update φ continuous_id)

/-- **A hard indicator of a price is not an expressible feature** (D3): no `e : EF` denotes
`1[t < V n φ]` on every history. `EF.denote` is continuous in the product topology
(FAF `EF.continuous_denote`), and along the path that varies only `V n φ` the indicator jumps
at `t`. About trade weights (`EF`), not LUVs.
Source: root-deference-2-002; [[li-deference]] line 115 ("fuzzy indicators")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem not_exists_ef_hardIndicator (t : ℝ) (n : ℕ) (φ : Sentence) :
    ¬ ∃ e : EF, ∀ V : History, e.denote V = if t < V n φ then 1 else 0 := by
  rintro ⟨e, he⟩
  classical
  let V : History := fun _ _ => 0
  let γ : ℝ → History := fun s => Function.update V n (Function.update (V n) φ s)
  have hγ : Continuous γ := continuous_pricePath V n φ
  let g : ℝ → ℝ := fun s => e.denote (γ s)
  have hg : Continuous g := (EF.continuous_denote e).comp hγ
  have hval : ∀ s, g s = if t < s then 1 else 0 := by
    intro s
    simp only [g, he, γ, Function.update_self]
  have hgt : g t = 0 := by
    rw [hval]
    simp
  have h1 : Tendsto g (𝓝[>] t) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hval, if_pos (Set.mem_Ioi.1 hs)]
  have h0 : Tendsto g (𝓝[>] t) (𝓝 (g t)) :=
    (hg.tendsto t).mono_left nhdsWithin_le_nhds
  have := tendsto_nhds_unique h1 h0
  rw [hgt] at this
  exact one_ne_zero this

end Cleanroom.Found.LiAsympCalc
