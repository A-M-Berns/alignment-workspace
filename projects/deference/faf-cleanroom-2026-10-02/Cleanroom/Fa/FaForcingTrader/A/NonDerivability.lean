import Cleanroom.Fa.FaForcingTrader.A.TheoremSS
import Cleanroom.Found.LiAsympCalc.Spikes
import Cleanroom.Found.LiAsympCalc.LimitPoint

/-!
# `fa-forcing-trader` · angle A · NonDerivability: averaged ⇏ per-day, scheduled ⇏ per-day, the one big lie (T8)

Real-sequence witnesses, no FAF content. Each inhabits the **abstract premise set** of Theorem SS
(averaged inputs on a gate — at full-limit grade where stated — and the quote above the threshold
on the support) and refutes the stronger per-day conclusion. Whether a logical-inductor pair
realizes any of them is OP9 (vq-wiki-055 (c)): **open**, recorded in prose, not as a `sorry`.

* `averaged_not_perDay` (Prop 7.1, vq-wiki-055 (b)): `D` = the squares (density `0`, infinite),
  `a ≡ 1`, `h = 1` off `D` and `0` on `D`, gate `≡ 1`, threshold `3/4`: Half 1 holds as a full
  limit, the averaged above-threshold inequality holds eventually, and the per-day target fails
  on `D` at margin `1/2`.
* `scheduled_averaged_not_perDay` (vq-wiki-2-011): the same on the sparse schedule
  `d k = 2k + 2` with `D` inside `im d`: both inputs hold with full limits *along the schedule*,
  per-day still fails on the scheduled days `d (k²)`.
* `two_limit_points_permanent_violation` (Prop 5.4, vq-wiki-055 (a)): `Y` = li-asymp-calc's
  cluster sequence, whose Cesàro mean oscillates between `≤ 3/8` and `≥ 2/3`; `a ≡ 2/3`,
  `h ≡ 3/8`, `t = 1/2`: both unbiasedness premises hold as limit points (on disjoint
  subsequences) and the quote is above `t` always, yet `h < t − 1/8` on every day — even the
  averaged conclusion fails. Two limit points, on unrelated subsequences, close nothing.
* `one_big_lie` (root-deference-057 (i)): a single day with error `B` (any size) leaves the
  all-days averaged error tending to `0`.
-/

namespace Cleanroom.Fa.FaForcingTrader.A

open LogicalInduction LogicalInduction.AffineCombination Cleanroom.Fa.FaTheoremA
  Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice
  Cleanroom.Fa.FaForcingTrader Filter Topology

/-- `weightedAverage 1 x n = cesaro x (n + 1)`.
Source: none: infrastructure (li-asymp-calc `cesaro_eq_weightedAverage_one`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem weightedAverage_one_eq_cesaro (x : ℕ → ℝ) (n : ℕ) :
    weightedAverage (fun _ => 1) x n = cesaro x (n + 1) := by
  rw [cesaro_eq_weightedAverage_one x (by omega : 1 ≤ n + 1)]
  simp

/-- A Cesàro limit is a limit of the all-days weighted average.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem tendsto_weightedAverage_one_of_cesaro {x : ℕ → ℝ} {l : ℝ}
    (h : Tendsto (cesaro x) atTop (𝓝 l)) :
    Tendsto (weightedAverage (fun _ => 1) x) atTop (𝓝 l) := by
  refine (h.comp (tendsto_add_atTop_nat 1)).congr (fun n => ?_)
  simp [Function.comp, weightedAverage_one_eq_cesaro]

/-! ## A. Prop 7.1: averaged ⇏ per-day -/

/-- **T8 (Prop 7.1). Averaged trust does not entail per-day trust.** With `a ≡ 1`,
`h = sqExc` (`1` off the squares, `0` on them), gate `≡ 1`, threshold `3/4`: (i) Half 1 holds as
a **full limit** (`WeightedApprox`); (ii) the averaged above-threshold inequality holds
**eventually**; (iii) the per-day target `h_n ≥ 3/4 − ρ` fails on the squares at margin `1/2`,
infinitely often. The premise set is the abstract one; realizability by inductors is OP9 (open).
Source: vq-wiki-055 (b) (Prop 7.1); [[route-recurring-ccee]] §5.5; li-asymp-calc `squareSpikes_witness`
Kind: N+
Fidelity: exact (the source's density-`0` set `D` is the squares)
Hyps: n/a -/
theorem averaged_not_perDay :
    WeightedApprox (fun _ => (1 : ℝ)) (fun _ => 1) sqExc ∧
      (∀ ρ : ℝ, 0 < ρ → ∀ᶠ n in atTop, 3 / 4 - ρ ≤ weightedAverage (fun _ => 1) sqExc n) ∧
      (∃ᶠ n in atTop, sqExc n ≤ 3 / 4 - 1 / 2) := by
  have hfull : WeightedApprox (fun _ => (1 : ℝ)) (fun _ => 1) sqExc := by
    show Tendsto (weightedAverage (fun _ => 1) (fun i => 1 - sqExc i)) atTop (𝓝 0)
    have hfun : (fun i => 1 - sqExc i) = squareSpikes := by
      funext i
      simp [sqExc]
    rw [hfun]
    exact tendsto_weightedAverage_one_of_cesaro squareSpikes_witness.2.2
  refine ⟨hfull, ?_, ?_⟩
  · exact schedThresholdAbove_eventually_of_fullLimit (fun _ => zero_le_one) tendsto_prefixSum_one
      (fun _ _ => by norm_num) hfull
  · rw [frequently_atTop]
    intro a
    refine ⟨a * a, Nat.le_mul_self a, ?_⟩
    unfold sqExc
    rw [squareSpikes_witness.2.1 a]
    norm_num

/-! ## B. The scheduled restriction (vq-wiki-2-011) -/

/-- `H`'s credence on the schedule `d k = 2k + 2`: `sqExc k` on day `d k` (`0` when `k` is a
square, `1` otherwise); the value off the schedule is irrelevant.
Source: vq-wiki-2-011
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def schedH (n : ℕ) : ℝ := sqExc (n / 2 - 1)

/-- **T8 (scheduled). Sparsity upgrades the inputs to full limits along the schedule and still
does not entail per-day trust.** On `d = linearSchedule 0` (window-disjoint for the successor
lookahead) with gate `w = 1[n ∈ im d]`: `w` has divergent mass, Half 1 holds as a full limit on
`w` (transferred from the feedback clock by FAF's `weightedAverage_supported_asympEq_zero_of_feedback`),
the averaged above-threshold inequality at `3/4` holds eventually, and the per-day target fails on
the scheduled days `d (k²)` at margin `1/2`.
Source: vq-wiki-2-011; vq-wiki-055 (b)
Kind: N+
Fidelity: exact
Hyps: n/a -/
theorem scheduled_averaged_not_perDay :
    WindowDisjoint succDeferral (linearSchedule 0) ∧
      Tendsto (prefixSum (schedInd (linearSchedule 0))) atTop atTop ∧
      WeightedApprox (schedInd (linearSchedule 0)) (fun _ => 1) schedH ∧
      (∀ ρ : ℝ, 0 < ρ → ∀ᶠ n in atTop,
        3 / 4 - ρ ≤ weightedAverage (schedInd (linearSchedule 0)) schedH n) ∧
      (∃ᶠ n in atTop, 0 < schedInd (linearSchedule 0) n ∧ schedH n ≤ 3 / 4 - 1 / 2) := by
  have hwd := windowDisjoint_succ_linear 0
  have hdiv : Tendsto (prefixSum (schedInd (linearSchedule 0))) atTop atTop := by
    have := (scheduleIndicator_divergent (linearSchedule 0) (fun _ _ => 0)).2
    simpa only [scheduleIndicator_denote] using this
  have hd : ∀ k, (linearSchedule 0).f k = 2 * k + 2 := fun k => by
    rw [linearSchedule_apply]
  have hschedH : ∀ k, schedH ((linearSchedule 0).f k) = sqExc k := fun k => by
    rw [hd, schedH]
    congr 1
    omega
  have hfull : WeightedApprox (schedInd (linearSchedule 0)) (fun _ => 1) schedH := by
    show Tendsto (weightedAverage (schedInd (linearSchedule 0)) (fun i => 1 - schedH i))
      atTop (𝓝 0)
    have hsupport : ∀ n, schedInd (linearSchedule 0) n ≠ 0 → ∃ j, (linearSchedule 0).f j = n :=
      fun n hn => (schedInd_ne_zero_iff _ n).1 hn
    have hsparse : feedbackWeightedAverage (fun k => schedInd (linearSchedule 0)
        ((linearSchedule 0).f k)) (fun k => 1 - schedH ((linearSchedule 0).f k)) ≈ₙ
        (fun _ => 0) := by
      show Tendsto (fun K => _ - (0 : ℝ)) atTop (𝓝 0)
      simp only [sub_zero]
      have hident : ∀ K, feedbackWeightedAverage (fun k => schedInd (linearSchedule 0)
          ((linearSchedule 0).f k)) (fun k => 1 - schedH ((linearSchedule 0).f k)) K =
          cesaro squareSpikes K := by
        intro K
        unfold feedbackWeightedAverage feedbackPrefixSum cesaro
        simp only [schedInd_of_mem, hschedH, one_mul, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, mul_one]
        have hsq : ∀ k, (1 : ℝ) - sqExc k = squareSpikes k := fun k => by simp [sqExc]
        simp only [hsq]
        split_ifs with hK
        · have : K = 0 := by exact_mod_cast hK
          subst this
          simp
        · rfl
      exact (squareSpikes_witness.2.2).congr (fun K => (hident K).symm)
    have hres := weightedAverage_supported_asympEq_zero_of_feedback
      (w := schedInd (linearSchedule 0)) (x := fun i => 1 - schedH i) hwd.1 hsupport hsparse
    have hres' : Tendsto (fun n => weightedAverage (schedInd (linearSchedule 0))
        (fun i => 1 - schedH i) n - 0) atTop (𝓝 0) := hres
    simpa only [sub_zero] using hres'
  refine ⟨hwd, hdiv, hfull, ?_, ?_⟩
  · exact schedThresholdAbove_eventually_of_fullLimit (fun n => (schedInd_mem_Icc _ n).1) hdiv
      (fun _ _ => by norm_num) hfull
  · rw [frequently_atTop]
    intro a
    refine ⟨(linearSchedule 0).f (a * a), le_trans (Nat.le_mul_self a)
      ((linearSchedule 0).lt (a * a)).le, ?_, ?_⟩
    · rw [schedInd_of_mem]
      norm_num
    · rw [hschedH]
      unfold sqExc
      rw [squareSpikes_witness.2.1 a]
      norm_num

/-! ## C. Prop 5.4: two limit points on disjoint subsequences -/

/-- The Cesàro mean of the cluster sequence is frequently `≤ 3/8` and frequently `≥ 2/3`.
Source: li-asymp-calc `clusterSeq_avg_even` / `clusterSeq_avg_odd`
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem clusterSeq_avg_frequently :
    (∃ᶠ n in atTop, weightedAverage (fun _ => 1) clusterSeq n ≤ 3 / 8) ∧
      (∃ᶠ n in atTop, 2 / 3 ≤ weightedAverage (fun _ => 1) clusterSeq n) := by
  constructor
  · rw [frequently_atTop]
    intro a
    refine ⟨4 ^ (a + 2) - 1, ?_, clusterSeq_avg_even (a + 2) (by omega)⟩
    have := le_four_pow (a + 2)
    omega
  · rw [frequently_atTop]
    intro a
    refine ⟨2 * 4 ^ a - 1, ?_, clusterSeq_avg_odd a⟩
    have := le_four_pow a
    omega

/-- Steps of the all-days Cesàro mean of the cluster sequence tend to `0`.
Source: FAF `weightedAverage_step_tendsto_zero`
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem clusterSeq_avg_step :
    Tendsto (fun n => weightedAverage (fun _ => 1) clusterSeq (n + 1) -
      weightedAverage (fun _ => 1) clusterSeq n) atTop (𝓝 0) :=
  weightedAverage_step_tendsto_zero (fun _ => 1) clusterSeq 1 (fun _ => zero_le_one)
    (fun _ => le_rfl) clusterSeq_abs_le tendsto_prefixSum_one

/-- `weightedBias 1 (const c) x n = c − avg x n` and `weightedBias 1 x (const c) n = avg x n − c`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem weightedBias_one_const (c : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    weightedBias (fun _ => 1) (fun _ => c) x n = c - weightedAverage (fun _ => 1) x n ∧
      weightedBias (fun _ => 1) x (fun _ => c) n = weightedAverage (fun _ => 1) x n - c := by
  have hden : prefixSum (fun _ : ℕ => (1 : ℝ)) n ≠ 0 := by
    rw [prefixSum_one]
    positivity
  constructor
  · show weightedAverage (fun _ => 1) (fun i => c - x i) n = _
    rw [weightedAverage_sub _ _ _ hden, weightedAverage_const _ _ hden]
  · show weightedAverage (fun _ => 1) (fun i => x i - c) n = _
    rw [weightedAverage_sub _ _ _ hden, weightedAverage_const _ _ hden]

/-- **T8 (Prop 5.4). Two limit points on unrelated subsequences close nothing.** With
`Y = clusterSeq`, `a ≡ 2/3`, `h ≡ 3/8`, gate `≡ 1`, `t = 1/2`: `0` is a limit point of the
averaged `a − Y` (the `A`-side premise, 4.8.15's shape) and of the averaged `Y − h` (the `H`-side
premise), and `a > t` on every day — yet `h ≤ t − 1/8` on every day, and even the averaged
conclusion `SchedThresholdAbove 1 h (1/2)` fails. The premise set is the abstract one
(vq-wiki-055 (a)); realizability by inductors is OP9 (open).
Source: vq-wiki-055 (a) (Prop 5.4); [[route-recurring-ccee]] §5.5 ("`N_A` and `N_H` are disjoint"); li-asymp-calc `clusterSeq_hasLimitPoint_not_tendsto`
Kind: N+
Fidelity: variant: doubling clusters (li-asymp-calc's) in place of the source's greedy blocks; same mechanism
Hyps: n/a -/
theorem two_limit_points_permanent_violation :
    HasLimitPoint (weightedBias (fun _ => 1) (fun _ => (2 / 3 : ℝ)) clusterSeq) 0 ∧
      HasLimitPoint (weightedBias (fun _ => 1) clusterSeq (fun _ => (3 / 8 : ℝ))) 0 ∧
      (∀ n : ℕ, (1 / 2 : ℝ) < (fun _ : ℕ => (2 / 3 : ℝ)) n) ∧
      (∀ n : ℕ, (fun _ : ℕ => (3 / 8 : ℝ)) n ≤ 1 / 2 - 1 / 8) ∧
      ¬ SchedThresholdAbove (fun _ => 1) (fun _ => (3 / 8 : ℝ)) (1 / 2) := by
  obtain ⟨hlow, hhigh⟩ := clusterSeq_avg_frequently
  have hstep := clusterSeq_avg_step
  refine ⟨?_, ?_, fun _ => by norm_num, fun _ => by norm_num, ?_⟩
  · have hf : (fun n => weightedBias (fun _ => 1) (fun _ => (2 / 3 : ℝ)) clusterSeq n) =
        fun n => 2 / 3 - weightedAverage (fun _ => 1) clusterSeq n :=
      funext (fun n => (weightedBias_one_const _ _ n).1)
    rw [show weightedBias (fun _ => 1) (fun _ => (2 / 3 : ℝ)) clusterSeq =
      fun n => 2 / 3 - weightedAverage (fun _ => 1) clusterSeq n from hf]
    refine hasLimitPoint_zero_of_two_sided_recurring _ ?_ ?_ ?_
    · have := hstep.neg
      rw [neg_zero] at this
      refine this.congr (fun n => ?_)
      ring
    · intro ε hε
      exact hlow.mono (fun n hn => by linarith)
    · intro ε hε
      exact hhigh.mono (fun n hn => by linarith)
  · have hf : (fun n => weightedBias (fun _ => 1) clusterSeq (fun _ => (3 / 8 : ℝ)) n) =
        fun n => weightedAverage (fun _ => 1) clusterSeq n - 3 / 8 :=
      funext (fun n => (weightedBias_one_const _ _ n).2)
    rw [show weightedBias (fun _ => 1) clusterSeq (fun _ => (3 / 8 : ℝ)) =
      fun n => weightedAverage (fun _ => 1) clusterSeq n - 3 / 8 from hf]
    refine hasLimitPoint_zero_of_two_sided_recurring _ ?_ ?_ ?_
    · refine hstep.congr (fun n => ?_)
      ring
    · intro ε hε
      exact hhigh.mono (fun n hn => by linarith)
    · intro ε hε
      exact hlow.mono (fun n hn => by linarith)
  · intro h
    obtain ⟨n, hn⟩ := (h (1 / 16) (by norm_num)).exists
    have hden : prefixSum (fun _ : ℕ => (1 : ℝ)) n ≠ 0 := by
      rw [prefixSum_one]
      positivity
    rw [weightedAverage_const _ _ hden] at hn
    norm_num at hn

/-! ## D. The one big lie -/

/-- **T8 (the one big lie).** A single day with forecast error `B` — of any size — leaves the
all-days averaged error tending to `0`: `a ≡ 1`, `h = 1 − spike B k`, `WeightedApprox 1 a h`
while `a_k − h_k = B`. Averaging launders a lie of bounded size at one day; it is the per-day
form that would forbid it.
Source: root-deference-057 (i); li-asymp-calc `tendsto_cesaro_spike`
Kind: N+
Fidelity: exact
Hyps: n/a -/
theorem one_big_lie (B : ℝ) (k : ℕ) :
    WeightedApprox (fun _ => (1 : ℝ)) (fun _ => 1) (fun i => 1 - spike B k i) ∧
      (fun _ : ℕ => (1 : ℝ)) k - (fun i => 1 - spike B k i) k = B := by
  constructor
  · show Tendsto (weightedAverage (fun _ => 1) (fun i => 1 - (1 - spike B k i))) atTop (𝓝 0)
    have hfun : (fun i => 1 - (1 - spike B k i)) = spike B k := by
      funext i
      ring
    rw [hfun]
    exact tendsto_weightedAverage_one_of_cesaro (tendsto_cesaro_spike B k)
  · simp [spike]

end Cleanroom.Fa.FaForcingTrader.A
