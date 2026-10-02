import Cleanroom.Found.LiAsympCalc.WeightedAverage
import Mathlib.Data.Nat.Log

/-!
# B. The limit-point engine

Target B of [[li-asymp-calc-mandate]]: FAF's `HasLimitPoint f x` is `MapClusterPt x atTop f`.

* B0: `HasLimitPoint f 0 ↔ ∀ ε > 0, ∃ᶠ n in atTop, |f n| < ε` (the notes' `LimitPointZero`).
* B1: the **wash-out lemma**: a nonnegative divergent weighting `u` supported, from day `N` on,
  only where `err ≥ c > 0` has weighted averages eventually `≥ c/2`, hence `0` is *not* a limit
  point of `weightedAverage u err`. The early days are unconstrained (the wash-out is the
  content), and the conclusion is about `weightedAverage u err`, an object the hypotheses never
  name: not a squeeze. Both signs; B1′ is the `EF`/`weightedBias` corollary that contradicts
  `BoundedSequence.recurringunbiasednessexp`'s conclusion directly.
* B2: witnesses with an adverse prefix (`err = -100` for ten days), constant and non-constant
  divergent `u`.
* B3: **limit point is strictly weaker than limit**: the doubling-cluster `{0,1}` sequence
  `clusterSeq` (`1` on `[2^k, 2^{k+1})` for even `k`) has uniform averages oscillating between
  `≤ 3/8` and `≥ 2/3`, so `1/2 - average` has `0` as a limit point (FAF's crossing lemma
  `hasLimitPoint_zero_of_two_sided_recurring`) but does not tend to `0`.
-/

namespace Cleanroom.Found.LiAsympCalc

open LogicalInduction Filter Topology Finset

/-! ### B0 -/

/-- `0` is a limit point of `f` iff `f` is frequently within every `ε` of `0`
(FAF `HasLimitPoint` = `MapClusterPt 0 atTop f`, Mathlib `mapClusterPt_iff_frequently`).
Source: `lean-deference` `Staleness.lean:48` (`LimitPointZero`); [[li-asymp-calc-mandate]] B0
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem hasLimitPoint_zero_iff {f : ℕ → ℝ} :
    HasLimitPoint f 0 ↔ ∀ ε > 0, ∃ᶠ n in atTop, |f n| < ε := by
  rw [HasLimitPoint, mapClusterPt_iff_frequently]
  constructor
  · intro h ε hε
    refine (h (Metric.ball 0 ε) (Metric.ball_mem_nhds 0 hε)).mono (fun n hn => ?_)
    simpa [Metric.mem_ball, Real.dist_eq] using hn
  · intro h s hs
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.1 hs
    refine (h ε hε).mono (fun n hn => hsub ?_)
    simpa [Metric.mem_ball, Real.dist_eq] using hn

/-- A sequence tending to `0` has `0` as a limit point (the trivial direction; the converse
fails, B3).
Source: [[li-asymp-calc-mandate]] B0
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem hasLimitPoint_zero_of_tendsto {f : ℕ → ℝ} (h : Tendsto f atTop (𝓝 0)) :
    HasLimitPoint f 0 :=
  h.mapClusterPt

/-! ### B1. The wash-out lemma -/

/-- Wash-out, quantitative core: from day `N` on, `c * prefixSum u n + D ≤ prefixSum (u·err) n`
where `D = ∑ i < N, u i * (err i - c)` is the (possibly negative) early-day debt.
Source: `lean-deference` `Staleness.lean:94–161`
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma washout_prefixSum_lower {u err : ℕ → ℝ} {c : ℝ} {N : ℕ} (hu : ∀ n, 0 ≤ u n)
    (hsupp : ∀ n, N ≤ n → 0 < u n → c ≤ err n) {n : ℕ} (hn : N ≤ n) :
    c * prefixSum u n + ∑ i ∈ range N, u i * (err i - c) ≤
      prefixSum (fun i => u i * err i) n := by
  have hpt : ∀ i, c * u i + (if i < N then u i * (err i - c) else 0) ≤ u i * err i := by
    intro i
    split_ifs with hi
    · have : c * u i + u i * (err i - c) = u i * err i := by ring
      linarith
    · rcases (hu i).lt_or_eq with hpos | hzero
      · have := hsupp i (not_lt.1 hi) hpos
        nlinarith [hu i]
      · rw [← hzero]
        simp
  have hfilt : (range (n + 1)).filter (fun i => i < N) = range N := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  calc c * prefixSum u n + ∑ i ∈ range N, u i * (err i - c)
      = ∑ i ∈ range (n + 1), (c * u i + if i < N then u i * (err i - c) else 0) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter, hfilt]
        rfl
    _ ≤ ∑ i ∈ range (n + 1), u i * err i := Finset.sum_le_sum (fun i _ => hpt i)

/-- **Wash-out lemma** (B1 (i)): `0 < c`, `u ≥ 0` with divergent mass, and from day `N` on
`u` supported only where `c ≤ err` ⟹ eventually `c / 2 ≤ weightedAverage u err n`. The first
`N` days are unconstrained.
Source: `lean-deference` `Staleness.lean:94–161`; [[fa-positive-results-corrected-v3]] §3
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem washout_eventually {u err : ℕ → ℝ} {c : ℝ} (hc : 0 < c) (N : ℕ) (hu : ∀ n, 0 ≤ u n)
    (hdiv : Tendsto (prefixSum u) atTop atTop)
    (hsupp : ∀ n, N ≤ n → 0 < u n → c ≤ err n) :
    ∀ᶠ n in atTop, c / 2 ≤ weightedAverage u err n := by
  have hDlim : Tendsto (fun n => (∑ i ∈ range N, u i * (err i - c)) / prefixSum u n)
      atTop (𝓝 0) := hdiv.const_div_atTop _
  have hev := hDlim.eventually (lt_mem_nhds (by linarith : -(c / 2) < (0 : ℝ)))
  filter_upwards [eventually_prefixSum_pos hdiv, hev, eventually_ge_atTop N] with n hpos hDn hNn
  rw [weightedAverage_eq_div hpos.ne', le_div_iff₀ hpos]
  have h1 := washout_prefixSum_lower hu hsupp hNn
  have h3 : -(c / 2) * prefixSum u n < ∑ i ∈ range N, u i * (err i - c) :=
    (lt_div_iff₀ hpos).1 hDn
  linarith

/-- **Wash-out lemma** (B1 (ii)): under the hypotheses of `washout_eventually`, `0` is not a
limit point of `weightedAverage u err`.
Source: `lean-deference` `Staleness.lean:94–161`; [[fa-positive-results-corrected-v3]] §3
Kind: P
Fidelity: exact (stated at the limit point, where the earlier Lean assumed a full limit)
Hyps: (a) none -/
theorem washout_not_hasLimitPoint {u err : ℕ → ℝ} {c : ℝ} (hc : 0 < c) (N : ℕ)
    (hu : ∀ n, 0 ≤ u n) (hdiv : Tendsto (prefixSum u) atTop atTop)
    (hsupp : ∀ n, N ≤ n → 0 < u n → c ≤ err n) :
    ¬ HasLimitPoint (weightedAverage u err) 0 := by
  intro h
  have hfreq := (hasLimitPoint_zero_iff.1 h) (c / 2) (by linarith)
  obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually (washout_eventually hc N hu hdiv hsupp)).exists
  have := abs_lt.1 hn1
  linarith [this.2]

/-- Wash-out, the other sign: support only where `err ≤ -c` from day `N` on.
Source: `lean-deference` `Staleness.lean:94–161`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem washout_not_hasLimitPoint_neg {u err : ℕ → ℝ} {c : ℝ} (hc : 0 < c) (N : ℕ)
    (hu : ∀ n, 0 ≤ u n) (hdiv : Tendsto (prefixSum u) atTop atTop)
    (hsupp : ∀ n, N ≤ n → 0 < u n → err n ≤ -c) :
    ¬ HasLimitPoint (weightedAverage u err) 0 := by
  have hneg := washout_not_hasLimitPoint hc N hu hdiv
    (err := fun i => -err i) (fun n hn hpos => by linarith [hsupp n hn hpos])
  intro h
  apply hneg
  rw [hasLimitPoint_zero_iff] at h ⊢
  intro ε hε
  refine (h ε hε).mono (fun n hn => ?_)
  rwa [weightedAverage_neg, abs_neg]

/-- B1′: a **divergent weighting cannot be supported, from some day on, where the bias is
one-signed and bounded away from zero** — in FAF's `weightedBias` spelling, so it contradicts
`BoundedSequence.recurringunbiasednessexp`'s `HasLimitPoint (weightedBias …) 0` directly. The
hypothesis is FAF's `DivergentWeighting W P` only: this is pure analysis and holds for every
divergent weighting; generability (`PGenerableWeighting`) is `recurringunbiasednessexp`'s
hypothesis, not this lemma's. No `IsLogicalInductor` instance here; the composition is
`fa-theorem-a`'s.
Source: [[fa-positive-results-corrected-v3]] §3; [[li-asymp-calc-mandate]] B1′
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem DivergentWeighting.not_hasLimitPoint_weightedBias {W : ℕ → EF} {P : History}
    (hW : DivergentWeighting W P) {market truth : ℕ → ℝ} {c : ℝ} (hc : 0 < c) (N : ℕ)
    (hsupp : ∀ n, N ≤ n → 0 < (W n).denote P → c ≤ market n - truth n) :
    ¬ HasLimitPoint (weightedBias (fun i => (W i).denote P) market truth) 0 := by
  unfold weightedBias
  exact washout_not_hasLimitPoint hc N (fun i => (hW.1 i).1) hW.2 hsupp

/-- B1′, the other sign (`market - truth ≤ -c` on the support).
Source: [[li-asymp-calc-mandate]] B1′
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem DivergentWeighting.not_hasLimitPoint_weightedBias_neg {W : ℕ → EF} {P : History}
    (hW : DivergentWeighting W P) {market truth : ℕ → ℝ} {c : ℝ} (hc : 0 < c) (N : ℕ)
    (hsupp : ∀ n, N ≤ n → 0 < (W n).denote P → market n - truth n ≤ -c) :
    ¬ HasLimitPoint (weightedBias (fun i => (W i).denote P) market truth) 0 := by
  unfold weightedBias
  exact washout_not_hasLimitPoint_neg hc N (fun i => (hW.1 i).1) hW.2 hsupp

/-! ### B2. Wash-out witnesses -/

/-- The uniform weighting has prefix sums `n + 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma prefixSum_one (n : ℕ) : prefixSum (fun _ : ℕ => (1 : ℝ)) n = (n : ℝ) + 1 := by
  rw [prefixSum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  push_cast
  ring

/-- The uniform weighting diverges.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma tendsto_prefixSum_one : Tendsto (prefixSum (fun _ : ℕ => (1 : ℝ))) atTop atTop := by
  refine (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).congr
    (fun n => ?_)
  rw [prefixSum_one]

/-- The uniform weighted average is the inclusive mean `(∑ i ≤ n, x i) / (n + 1)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma weightedAverage_one (x : ℕ → ℝ) (n : ℕ) :
    weightedAverage (fun _ => 1) x n = (∑ i ∈ range (n + 1), x i) / ((n : ℝ) + 1) := by
  rw [weightedAverage_eq_div (by rw [prefixSum_one]; positivity), prefixSum_one]
  simp [prefixSum]

/-- Adverse-prefix error stream: `-100` for the first ten days, then `1`.
Source: `lean-deference` `Staleness.lean:237`
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def adverseErr (n : ℕ) : ℝ := if n < 10 then -100 else 1

/-- **B2 (N−, the source's witness)**: the wash-out lemma's full hypothesis package with the
uniform weighting, `c = 1`, `N = 10`, and an error stream that is negative on the first ten
days (`∃ n, err n < 0`, so the early days really are unconstrained); conclusion: `0` is not a
limit point. Graded N− because the weighting `u ≡ 1` is constant (the mandate calls it
degenerate); it is kept for fidelity to lean-deference-031. The N+ witness is
`washout_witness_harmonic` (non-constant divergent `u`).
Source: `lean-deference` `Staleness.lean:237`; [[li-asymp-calc-mandate]] B2
Kind: N-
Fidelity: n/a
Hyps: n/a -/
theorem washout_witness_uniform :
    (∀ n, 0 ≤ (fun _ : ℕ => (1 : ℝ)) n) ∧
      Tendsto (prefixSum (fun _ : ℕ => (1 : ℝ))) atTop atTop ∧
      (∀ n, 10 ≤ n → 0 < (fun _ : ℕ => (1 : ℝ)) n → (1 : ℝ) ≤ adverseErr n) ∧
      (∃ n, adverseErr n < 0) ∧
      ¬ HasLimitPoint (weightedAverage (fun _ => 1) adverseErr) 0 := by
  have hsupp : ∀ n, 10 ≤ n → 0 < (fun _ : ℕ => (1 : ℝ)) n → (1 : ℝ) ≤ adverseErr n := by
    intro n hn _
    simp [adverseErr, not_lt.2 hn]
  refine ⟨fun _ => zero_le_one, tendsto_prefixSum_one, hsupp, ⟨0, by simp [adverseErr]⟩, ?_⟩
  exact washout_not_hasLimitPoint one_pos 10 (fun _ => zero_le_one) tendsto_prefixSum_one hsupp

/-- The harmonic weighting `u n = 1 / (n + 1)`: non-constant, nonnegative, divergent mass.
Source: [[li-asymp-calc-mandate]] B2
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma harmonicWeight_divergent :
    Tendsto (prefixSum (fun n : ℕ => 1 / ((n : ℝ) + 1))) atTop atTop :=
  Real.tendsto_sum_range_one_div_nat_succ_atTop.comp (tendsto_add_atTop_nat 1)

/-- **B2 (N+, non-constant weighting)**: the wash-out package with the harmonic weighting
`u n = 1/(n+1)` (strictly decreasing, so not a constant witness) and the adverse-prefix errors.
Source: [[li-asymp-calc-mandate]] B2
Kind: N+
Fidelity: n/a
Hyps: n/a -/
theorem washout_witness_harmonic :
    (∀ n, 0 ≤ (fun n : ℕ => 1 / ((n : ℝ) + 1)) n) ∧
      Tendsto (prefixSum (fun n : ℕ => 1 / ((n : ℝ) + 1))) atTop atTop ∧
      (∀ n, 10 ≤ n → 0 < (fun n : ℕ => 1 / ((n : ℝ) + 1)) n → (1 : ℝ) ≤ adverseErr n) ∧
      (∃ n, adverseErr n < 0) ∧
      (∀ n, (fun n : ℕ => 1 / ((n : ℝ) + 1)) (n + 1) < (fun n : ℕ => 1 / ((n : ℝ) + 1)) n) ∧
      ¬ HasLimitPoint (weightedAverage (fun n : ℕ => 1 / ((n : ℝ) + 1)) adverseErr) 0 := by
  have hu : ∀ n, 0 ≤ (fun n : ℕ => 1 / ((n : ℝ) + 1)) n := fun n => by positivity
  have hsupp : ∀ n, 10 ≤ n → 0 < (fun n : ℕ => 1 / ((n : ℝ) + 1)) n → (1 : ℝ) ≤ adverseErr n := by
    intro n hn _
    simp [adverseErr, not_lt.2 hn]
  refine ⟨hu, harmonicWeight_divergent, hsupp, ⟨0, by simp [adverseErr]⟩, fun n => ?_, ?_⟩
  · apply one_div_lt_one_div_of_lt
    · positivity
    · push_cast
      linarith
  · exact washout_not_hasLimitPoint one_pos 10 hu harmonicWeight_divergent hsupp

/-! ### B3. Limit point is strictly weaker than limit -/

/-- The doubling-cluster sequence: `1` on `[2^k, 2^{k+1})` for even `k` (and at `0`), `0` for
odd `k`. Its uniform averages oscillate between about `1/3` and `2/3`.
Source: lean-deference-2-012 (a); [[li-asymp-calc-mandate]] B3
Kind: D
Fidelity: variant: doubling clusters in place of the source's `10^k` clusters
Hyps: n/a -/
noncomputable def clusterSeq (n : ℕ) : ℝ := if Even (Nat.log 2 n) then 1 else 0

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma clusterSeq_mem (n : ℕ) : clusterSeq n = 0 ∨ clusterSeq n = 1 := by
  unfold clusterSeq
  split_ifs <;> simp

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma clusterSeq_abs_le (n : ℕ) : |clusterSeq n| ≤ 1 := by
  rcases clusterSeq_mem n with h | h <;> rw [h] <;> norm_num

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma clusterSeq_of_mem_Ico {m n : ℕ} (h1 : 2 ^ m ≤ n) (h2 : n < 2 ^ (m + 1)) :
    clusterSeq n = if Even m then 1 else 0 := by
  unfold clusterSeq
  rw [Nat.log_eq_of_pow_le_of_lt_pow h1 h2]

/-- Sum of `clusterSeq` over `[0, 2^m)`: `1` (from `n = 0`) plus `2^k` for each even `k < m`. -/
lemma clusterSeq_sum_pow (m : ℕ) :
    ∑ n ∈ range (2 ^ m), clusterSeq n =
      1 + ∑ k ∈ range m, (if Even k then (2 : ℝ) ^ k else 0) := by
  induction m with
  | zero =>
    rw [pow_zero, Finset.sum_range_one, Finset.sum_range_zero, add_zero]
    simp [clusterSeq]
  | succ m ih =>
    have hle : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ m)
    rw [← Finset.sum_range_add_sum_Ico _ hle, ih, Finset.sum_range_succ]
    have hblock : ∑ n ∈ Ico (2 ^ m) (2 ^ (m + 1)), clusterSeq n =
        if Even m then (2 : ℝ) ^ m else 0 := by
      rw [Finset.sum_congr rfl (fun n hn => clusterSeq_of_mem_Ico (Finset.mem_Ico.1 hn).1
        (Finset.mem_Ico.1 hn).2)]
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      have hcard : 2 ^ (m + 1) - 2 ^ m = 2 ^ m := by
        rw [pow_succ]
        omega
      rw [hcard]
      push_cast
      split_ifs <;> simp
    rw [hblock]
    ring

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma evenPowSum_two_mul (j : ℕ) :
    3 * (∑ k ∈ range (2 * j), (if Even k then (2 : ℝ) ^ k else 0)) = 4 ^ j - 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      if_pos (even_two_mul j), if_neg (by simp)]
    have h4 : (2 : ℝ) ^ (2 * j) = 4 ^ j := by
      rw [pow_mul]
      norm_num
    rw [pow_succ]
    linear_combination ih + 3 * h4

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma evenPowSum_two_mul_add_one (j : ℕ) :
    3 * (∑ k ∈ range (2 * j + 1), (if Even k then (2 : ℝ) ^ k else 0)) = 4 ^ (j + 1) - 1 := by
  rw [Finset.sum_range_succ, if_pos (even_two_mul j)]
  have h4 : (2 : ℝ) ^ (2 * j) = 4 ^ j := by
    rw [pow_mul]
    norm_num
  rw [pow_succ]
  linear_combination evenPowSum_two_mul j + 3 * h4

/-- The uniform average of `clusterSeq` at day `2^m - 1`. -/
lemma clusterSeq_avg (m : ℕ) :
    weightedAverage (fun _ => 1) clusterSeq (2 ^ m - 1) =
      (1 + ∑ k ∈ range m, (if Even k then (2 : ℝ) ^ k else 0)) / 2 ^ m := by
  have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rw [weightedAverage_one, Nat.sub_add_cancel hpos, clusterSeq_sum_pow]
  congr 1
  rw [Nat.cast_sub hpos]
  push_cast
  ring

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma clusterSeq_avg_even (j : ℕ) (hj : 2 ≤ j) :
    weightedAverage (fun _ => 1) clusterSeq (4 ^ j - 1) ≤ 3 / 8 := by
  have h4 : (4 : ℕ) ^ j = 2 ^ (2 * j) := by
    rw [pow_mul]
    norm_num
  rw [h4, clusterSeq_avg, div_le_iff₀ (by positivity)]
  have hS := evenPowSum_two_mul j
  have h4R : (2 : ℝ) ^ (2 * j) = 4 ^ j := by
    rw [pow_mul]
    norm_num
  have h16 : (16 : ℝ) ≤ 4 ^ j := by
    calc (16 : ℝ) = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ j := pow_le_pow_right₀ (by norm_num) hj
  rw [h4R]
  linarith

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma clusterSeq_avg_odd (j : ℕ) :
    2 / 3 ≤ weightedAverage (fun _ => 1) clusterSeq (2 * 4 ^ j - 1) := by
  have h4 : 2 * (4 : ℕ) ^ j = 2 ^ (2 * j + 1) := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [h4, clusterSeq_avg, le_div_iff₀ (by positivity)]
  have hS := evenPowSum_two_mul_add_one j
  have h4R : (2 : ℝ) ^ (2 * j + 1) = 2 * 4 ^ j := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [h4R, pow_succ] at *
  linarith

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma le_four_pow (a : ℕ) : a + 1 ≤ 4 ^ a := by
  induction a with
  | zero => norm_num
  | succ a ih =>
    rw [pow_succ]
    omega

/-- **B3 (N+)**: for the `{0,1}`-valued `clusterSeq`, `0` is a limit point of
`1/2 - weightedAverage 1 clusterSeq` but not its limit: the uniform average is frequently
`≤ 3/8` and frequently `≥ 2/3`, adjacent averages differ by `O(1/n)` (FAF
`weightedAverage_step_tendsto_zero`), and FAF's crossing lemma
`hasLimitPoint_zero_of_two_sided_recurring` gives the limit point. So `HasLimitPoint … 0`
(the conclusion of FAF's recurring-unbiasedness endpoints) is strictly weaker than
`Tendsto … (𝓝 0)`.
Source: lean-deference-2-012 (a); vq-wiki-2-001 (the six-carrier column contrast)
Kind: N+
Fidelity: variant: doubling clusters (the source's `10^k` clusters are `stretch`)
Hyps: n/a -/
theorem clusterSeq_hasLimitPoint_not_tendsto :
    (∀ n, clusterSeq n = 0 ∨ clusterSeq n = 1) ∧
    HasLimitPoint (fun n => 1 / 2 - weightedAverage (fun _ => 1) clusterSeq n) 0 ∧
    ¬ Tendsto (fun n => 1 / 2 - weightedAverage (fun _ => 1) clusterSeq n) atTop (𝓝 0) := by
  set f : ℕ → ℝ := fun n => 1 / 2 - weightedAverage (fun _ => 1) clusterSeq n with hf
  have hlow : ∃ᶠ n in atTop, 1 / 8 ≤ f n := by
    rw [frequently_atTop]
    intro a
    refine ⟨4 ^ (a + 2) - 1, ?_, ?_⟩
    · have := le_four_pow (a + 2)
      omega
    · have := clusterSeq_avg_even (a + 2) (by omega)
      simp only [hf]
      linarith
  have hup : ∃ᶠ n in atTop, f n ≤ -(1 / 6) := by
    rw [frequently_atTop]
    intro a
    refine ⟨2 * 4 ^ a - 1, ?_, ?_⟩
    · have := le_four_pow a
      omega
    · have := clusterSeq_avg_odd a
      simp only [hf]
      linarith
  refine ⟨clusterSeq_mem, ?_, ?_⟩
  · apply hasLimitPoint_zero_of_two_sided_recurring
    · have hstep := weightedAverage_step_tendsto_zero (fun _ => 1) clusterSeq 1
        (fun _ => zero_le_one) (fun _ => le_rfl) clusterSeq_abs_le tendsto_prefixSum_one
      have := hstep.neg
      rw [neg_zero] at this
      refine this.congr (fun n => ?_)
      simp only [hf]
      ring
    · intro ε hε
      exact hlow.mono (fun n hn => by linarith)
    · intro ε hε
      exact hup.mono (fun n hn => by linarith)
  · intro h
    have hev := h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
    obtain ⟨n, hn1, hn2⟩ := (hlow.and_eventually hev).exists
    linarith

end Cleanroom.Found.LiAsympCalc
