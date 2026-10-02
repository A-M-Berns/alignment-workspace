import Cleanroom.Found.LiAsympCalc.WeightedAverage
import Mathlib.Data.Nat.Find

/-!
# `trust-merge` · OneBigLie: asymptotic endorsement is silent about a single round (T7, 015)

**trust-lab-015 / [[merging-inductors-ideate]] Idea 6 ("the one big lie").** Every `≂_w`
endorsement is an average; "a treacherous trader with budget `b` defeated in the `≂_t` limit can
still make `B_T(φ_T)` wrong by up to `≈ b` on **one** decision". At the level of real sequences
this is a theorem about weighted averages: **for every `[0,1]`-valued divergent weighting `w` and
every `B > 0` there is a residual `r` with `|r| ≤ B`, `w`-average tending to `0`, and
`|r_n| = B` infinitely often** (`oneBigLie`). The spikes sit on an adaptive sparse set: the `k`-th
spike at the first day on which the prefix mass of `w` reaches `k²` (`spikeDay`), so that at most
`K` spikes are seen by the time the mass reaches `K²`, and the normalized spike mass is `≤ B/K`
(`bigLie_weightedAverage_le`). The construction uses `w ≤ 1` (so the prefix mass grows by at
most `1` a day) and divergence (so every `k²` is reached), nothing else.

**Shadow corollary over T1's objects** (`luvTotalTrustAvg_silent_shadow`): for any such `w` and
any margin `c ∈ (0, 1/2]` there are `[0,1]`-valued "market" and "truth" sequences with
`weightedBias w market truth → 0` — the conclusion of `QuoteUnbiased` / `LUVTotalTrustAvg` — yet
`truth_n − market_n = c` infinitely often. **Disclosed:** no inductor is constructed; the
statement is about the *grade* of the guarantee, not about a market that attains it. Whether a
logical inductor's actual residual against a determined quote can be `B` infinitely often under a
generable weighting is a question about FAF's `IsLogicalInductor` and is not settled here; what
is settled is that the averaged conclusion does not exclude it.

Mathlib and `li-asymp-calc` only.
-/

namespace Cleanroom.Trust.TrustMerge

open LogicalInduction Filter Topology Finset
open Cleanroom.Found.LiAsympCalc

noncomputable section

/-- A `[0,1]`-valued weighting's prefix mass grows by at most one a day: `prefixSum w n ≤ n + 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem prefixSum_le_succ {w : ℕ → ℝ} (hw : ∀ i, w i ≤ 1) (n : ℕ) :
    prefixSum w n ≤ (n : ℝ) + 1 := by
  unfold prefixSum
  calc ∑ i ∈ range (n + 1), w i ≤ ∑ _i ∈ range (n + 1), (1 : ℝ) :=
        sum_le_sum (fun i _ => hw i)
    _ = (n : ℝ) + 1 := by simp

/-- The prefix mass is monotone for a nonnegative weighting.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem prefixSum_mono {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) : Monotone (prefixSum w) := by
  intro m n hmn
  unfold prefixSum
  exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) (fun i _ _ => hw i)

section Construction

variable {w : ℕ → ℝ} (hdiv : Tendsto (prefixSum w) atTop atTop)
include hdiv

/-- Every level `k²` is reached by the prefix mass of a divergent weighting.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem exists_prefixSum_ge (k : ℕ) : ∃ n, ((k : ℝ)) ^ 2 ≤ prefixSum w n := by
  obtain ⟨N, hN⟩ := tendsto_atTop_atTop.1 hdiv ((k : ℝ) ^ 2)
  exact ⟨N, hN N le_rfl⟩

/-- **The `k`-th spike day**: the first day on which the prefix mass of `w` reaches `k²`.
Source: trust-lab-015 (the spike construction); `li-asymp-calc` `spike_family` (the pattern)
Kind: D
Fidelity: exact -/
def spikeDay (k : ℕ) : ℕ := Nat.find (exists_prefixSum_ge hdiv k)

/-- The spike day reaches its level.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem spikeDay_spec (k : ℕ) : ((k : ℝ)) ^ 2 ≤ prefixSum w (spikeDay hdiv k) :=
  Nat.find_spec (exists_prefixSum_ge hdiv k)

/-- Spike days are monotone in the level.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem spikeDay_mono {j k : ℕ} (hjk : j ≤ k) : spikeDay hdiv j ≤ spikeDay hdiv k := by
  unfold spikeDay
  apply Nat.find_mono
  intro n hn
  have hjk' : ((j : ℝ)) ^ 2 ≤ ((k : ℝ)) ^ 2 := by
    have : (j : ℝ) ≤ k := by exact_mod_cast hjk
    nlinarith [j.cast_nonneg (α := ℝ)]
  exact hjk'.trans hn

/-- The `k`-th spike day is at least `k² − 1` (the mass grows by at most one a day).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem spikeDay_ge (hw : ∀ i, w i ≤ 1) (k : ℕ) :
    ((k : ℝ)) ^ 2 ≤ (spikeDay hdiv k : ℝ) + 1 :=
  (spikeDay_spec hdiv k).trans (prefixSum_le_succ hw _)

/-- **The big-lie residual**: `B` on the spike days `spikeDay (k+1)`, `k ≥ 0`, and `0` elsewhere.
Source: trust-lab-015; [[merging-inductors-ideate]] Idea 6
Kind: D
Fidelity: exact -/
def bigLie (B : ℝ) (n : ℕ) : ℝ := by
  classical exact if ∃ k, spikeDay hdiv (k + 1) = n then B else 0

/-- The residual is bounded by `B`.
Source: trust-lab-015
Kind: L
Fidelity: n/a -/
theorem bigLie_abs_le {B : ℝ} (hB : 0 ≤ B) (n : ℕ) : |bigLie hdiv B n| ≤ B := by
  unfold bigLie
  split_ifs <;> simp [abs_of_nonneg hB, hB]

/-- The residual is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem bigLie_nonneg {B : ℝ} (hB : 0 ≤ B) (n : ℕ) : 0 ≤ bigLie hdiv B n := by
  unfold bigLie
  split_ifs <;> simp [hB]

/-- **The lie is told infinitely often**: beyond every day there is a spike day.
Source: trust-lab-015 ("silent about a single round" — infinitely many of them)
Kind: L
Fidelity: n/a -/
theorem bigLie_frequently (hw : ∀ i, w i ≤ 1) (B : ℝ) (N : ℕ) :
    ∃ n, N ≤ n ∧ bigLie hdiv B n = B := by
  refine ⟨spikeDay hdiv (N + 1), ?_, ?_⟩
  · have h := spikeDay_ge hdiv hw (N + 1)
    have hN : ((N : ℝ) + 1) ^ 2 ≤ (spikeDay hdiv (N + 1) : ℝ) + 1 := by exact_mod_cast h
    have : (N : ℝ) ≤ spikeDay hdiv (N + 1) := by nlinarith [N.cast_nonneg (α := ℝ)]
    exact_mod_cast this
  · unfold bigLie
    exact if_pos (⟨N, rfl⟩ : ∃ k, spikeDay hdiv (k + 1) = spikeDay hdiv (N + 1))

/-- The number of spike levels exhausted by day `N`: the least `k` whose `(k+1)`-st spike day lies
beyond `N` (exists because spike days are unbounded).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def spikeCount (hw : ∀ i, w i ≤ 1) (N : ℕ) : ℕ :=
  Nat.find (show ∃ k, ¬ spikeDay hdiv (k + 1) ≤ N from by
    refine ⟨N + 1, ?_⟩
    have h := spikeDay_ge hdiv hw (N + 1 + 1)
    intro hle
    have hle' : (spikeDay hdiv (N + 1 + 1) : ℝ) ≤ N := by exact_mod_cast hle
    push_cast at h
    nlinarith [N.cast_nonneg (α := ℝ)])

/-- Below the count every spike day is `≤ N`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem spikeDay_le_of_lt_spikeCount (hw : ∀ i, w i ≤ 1) {N k : ℕ}
    (hk : k < spikeCount hdiv hw N) : spikeDay hdiv (k + 1) ≤ N :=
  not_not.mp (Nat.find_min _ hk)

/-- At the count the spike day exceeds `N`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem spikeDay_spikeCount_gt (hw : ∀ i, w i ≤ 1) (N : ℕ) :
    N < spikeDay hdiv (spikeCount hdiv hw N + 1) := by
  have := Nat.find_spec (show ∃ k, ¬ spikeDay hdiv (k + 1) ≤ N from by
    refine ⟨N + 1, ?_⟩
    have h := spikeDay_ge hdiv hw (N + 1 + 1)
    intro hle
    have hle' : (spikeDay hdiv (N + 1 + 1) : ℝ) ≤ N := by exact_mod_cast hle
    push_cast at h
    nlinarith [N.cast_nonneg (α := ℝ)])
  exact not_le.1 this

/-- The spike days `≤ N` are the images of the levels below the count.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem spike_filter_subset (hw : ∀ i, w i ≤ 1) (N : ℕ)
    [DecidablePred (fun i => ∃ k, spikeDay hdiv (k + 1) = i)] :
    ((range (N + 1)).filter (fun i => ∃ k, spikeDay hdiv (k + 1) = i)) ⊆
      (range (spikeCount hdiv hw N)).image (fun k => spikeDay hdiv (k + 1)) := by
  intro i hi
  simp only [mem_filter, mem_range] at hi
  obtain ⟨hiN, k, hk⟩ := hi
  simp only [mem_image, mem_range]
  refine ⟨k, ?_, hk⟩
  by_contra hcontra
  push_neg at hcontra
  have h1 : spikeDay hdiv (spikeCount hdiv hw N + 1) ≤ spikeDay hdiv (k + 1) :=
    spikeDay_mono hdiv (by omega)
  have h2 := spikeDay_spikeCount_gt hdiv hw N
  omega

/-- The prefix mass dominates the square of the count.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem spikeCount_sq_le (hw0 : ∀ i, 0 ≤ w i) (hw : ∀ i, w i ≤ 1) (N : ℕ) :
    ((spikeCount hdiv hw N : ℕ) : ℝ) ^ 2 ≤ prefixSum w N := by
  rcases Nat.eq_zero_or_pos (spikeCount hdiv hw N) with h0 | hpos
  · rw [h0]
    simp only [Nat.cast_zero, zero_pow two_ne_zero]
    exact prefixSum_nonneg hw0 N
  · obtain ⟨K, hK⟩ : ∃ K, spikeCount hdiv hw N = K + 1 :=
      ⟨spikeCount hdiv hw N - 1, by omega⟩
    have hle : spikeDay hdiv (K + 1) ≤ N :=
      spikeDay_le_of_lt_spikeCount hdiv hw (by omega)
    have hspec := spikeDay_spec hdiv (K + 1)
    rw [hK]
    exact hspec.trans (prefixSum_mono hw0 hle)

/-- The count is unbounded.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem spikeCount_tendsto (hw : ∀ i, w i ≤ 1) :
    Tendsto (fun N => spikeCount hdiv hw N) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro k
  refine ⟨spikeDay hdiv (k + 1), fun N hN => ?_⟩
  by_contra hlt
  push_neg at hlt
  have h1 : spikeDay hdiv (spikeCount hdiv hw N + 1) ≤ spikeDay hdiv (k + 1) :=
    spikeDay_mono hdiv (by omega)
  have h2 := spikeDay_spikeCount_gt hdiv hw N
  omega

/-- **The normalized spike mass is at most `B / count`** on days where the count is positive.
Source: trust-lab-015 (the bound that makes the average vanish)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem bigLie_weightedAverage_le (hw0 : ∀ i, 0 ≤ w i) (hw : ∀ i, w i ≤ 1) {B : ℝ}
    (hB : 0 ≤ B) {N : ℕ} (hpos : 0 < spikeCount hdiv hw N) :
    weightedAverage w (bigLie hdiv B) N ≤ B / (spikeCount hdiv hw N : ℝ) := by
  classical
  set K := spikeCount hdiv hw N with hK
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hpos
  have hsN : (K : ℝ) ^ 2 ≤ prefixSum w N := spikeCount_sq_le hdiv hw0 hw N
  have hsNpos : 0 < prefixSum w N := by nlinarith
  -- numerator bound
  have hnum : prefixSum (fun i => w i * bigLie hdiv B i) N ≤ B * K := by
    unfold prefixSum
    have heq : ∀ i, w i * bigLie hdiv B i =
        if ∃ k, spikeDay hdiv (k + 1) = i then w i * B else 0 := by
      intro i
      unfold bigLie
      split_ifs <;> simp
    simp only [heq]
    rw [← Finset.sum_filter]
    calc ∑ i ∈ (range (N + 1)).filter (fun i => ∃ k, spikeDay hdiv (k + 1) = i), w i * B
        ≤ ∑ _i ∈ (range (N + 1)).filter (fun i => ∃ k, spikeDay hdiv (k + 1) = i), B :=
          sum_le_sum (fun i _ => by nlinarith [hw i, hw0 i])
      _ = (((range (N + 1)).filter (fun i => ∃ k, spikeDay hdiv (k + 1) = i)).card : ℝ) * B := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (K : ℝ) * B := by
          apply mul_le_mul_of_nonneg_right _ hB
          have hc := (card_le_card (spike_filter_subset hdiv hw N)).trans card_image_le
          rw [card_range] at hc
          exact_mod_cast hc
      _ = B * K := by ring
  rw [weightedAverage_eq_div hsNpos.ne']
  rw [div_le_div_iff₀ hsNpos hKpos]
  calc prefixSum (fun i => w i * bigLie hdiv B i) N * K ≤ B * K * K :=
        mul_le_mul_of_nonneg_right hnum hKpos.le
    _ = B * (K : ℝ) ^ 2 := by ring
    _ ≤ B * prefixSum w N := mul_le_mul_of_nonneg_left hsN hB

/-- **The big-lie residual averages to zero** under the weighting that built it.
Source: trust-lab-015
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem bigLie_tendsto (hw0 : ∀ i, 0 ≤ w i) (hw : ∀ i, w i ≤ 1) {B : ℝ} (hB : 0 ≤ B) :
    Tendsto (weightedAverage w (bigLie hdiv B)) atTop (𝓝 0) := by
  have hcount := spikeCount_tendsto hdiv hw
  have hbound : Tendsto (fun N => B / (spikeCount hdiv hw N : ℝ)) atTop (𝓝 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) B
    exact h.comp hcount
  refine squeeze_zero' ?_ ?_ hbound
  · filter_upwards with N
    rcases eq_or_ne (prefixSum w N) 0 with h0 | h0
    · simp [weightedAverage, h0]
    · rw [weightedAverage_eq_div h0]
      apply div_nonneg
      · unfold prefixSum
        exact sum_nonneg (fun i _ => mul_nonneg (hw0 i) (bigLie_nonneg hdiv hB i))
      · exact prefixSum_nonneg hw0 N
  · filter_upwards [hcount.eventually (eventually_gt_atTop 0)] with N hN
    exact bigLie_weightedAverage_le hdiv hw0 hw hB hN

end Construction

/-- **T7, 015 (headline). The one big lie:** for every `[0,1]`-valued divergent weighting `w` and
every `B > 0` there is a residual `r` with `|r_n| ≤ B` for all `n`, `w`-average tending to `0`,
and `|r_n| = B` beyond every day. The averaged grade of every endorsement in this package is
silent about any single round.
Source: trust-lab-015 ([[merging-inductors-ideate]] Idea 6, "the one big lie": "Endorsement is a
`≂_w` *average* statement; it is **silent about any single round**"); report §6.4
Kind: P
Fidelity: exact (real-sequence form)
Hyps: (a) none -/
theorem oneBigLie {w : ℕ → ℝ} (hmem : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (hdiv : Tendsto (prefixSum w) atTop atTop) {B : ℝ} (hB : 0 < B) :
    ∃ r : ℕ → ℝ, (∀ n, |r n| ≤ B) ∧ Tendsto (weightedAverage w r) atTop (𝓝 0) ∧
      ∀ N, ∃ n, N ≤ n ∧ |r n| = B :=
  ⟨bigLie hdiv B, bigLie_abs_le hdiv hB.le,
    bigLie_tendsto hdiv (fun i => (hmem i).1) (fun i => (hmem i).2) hB.le,
    fun N => by
      obtain ⟨n, hn, hr⟩ := bigLie_frequently hdiv (fun i => (hmem i).2) B N
      exact ⟨n, hn, by rw [hr, abs_of_pos hB]⟩⟩

/-- **Shadow over T1's objects (N+, no inductor):** for every `[0,1]`-valued divergent `w` and
margin `c ∈ (0, 1/2]` there are `[0,1]`-valued sequences `market` and `truth` with
`weightedBias w market truth → 0` — the conclusion of `QuoteUnbiased` / `LUVTotalTrustAvg` — yet
`truth_n − market_n = c` beyond every day. `LUVTotalTrustAvg` and classwise Value are consistent
with `𝔼^H_n(S_n) < 𝔼^H_n(O_n) − c` on infinitely many days. **Disclosed:** real sequences only;
whether an inductor's residual against a determined quote attains this is not settled here.
Source: trust-lab-015; mandate T7 ("a non-implication witnessed at the real-sequence level —
disclose that no inductor is constructed")
Kind: N+
Fidelity: weaker: shadow (no market)
Hyps: n/a -/
theorem luvTotalTrustAvg_silent_shadow {w : ℕ → ℝ} (hmem : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (hdiv : Tendsto (prefixSum w) atTop atTop) {c : ℝ} (hc : 0 < c) (hc' : c ≤ 1 / 2) :
    ∃ market truth : ℕ → ℝ, (∀ n, 0 ≤ market n ∧ market n ≤ 1) ∧
      (∀ n, 0 ≤ truth n ∧ truth n ≤ 1) ∧
      Tendsto (weightedBias w market truth) atTop (𝓝 0) ∧
      ∀ N, ∃ n, N ≤ n ∧ truth n - market n = c := by
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hmem i).1
  have hw1 : ∀ i, w i ≤ 1 := fun i => (hmem i).2
  refine ⟨fun n => 1 / 2 - bigLie hdiv c n, fun _ => 1 / 2, ?_, ?_, ?_, ?_⟩
  · intro n
    have h1 := bigLie_abs_le hdiv hc.le n
    have h2 := bigLie_nonneg hdiv hc.le n
    rw [abs_of_nonneg h2] at h1
    constructor <;> linarith
  · intro n; norm_num
  · have h := bigLie_tendsto hdiv hw0 hw1 hc.le
    have hneg : weightedBias w (fun n => 1 / 2 - bigLie hdiv c n) (fun _ => 1 / 2) =
        fun N => -weightedAverage w (bigLie hdiv c) N := by
      funext N
      unfold weightedBias
      rw [← weightedAverage_neg]
      congr 1
      funext i
      ring
    rw [hneg]
    simpa using h.neg
  · intro N
    obtain ⟨n, hn, hr⟩ := bigLie_frequently hdiv hw1 c N
    refine ⟨n, hn, ?_⟩
    show (1 / 2 : ℝ) - (1 / 2 - bigLie hdiv c n) = c
    rw [hr]
    ring

end

end Cleanroom.Trust.TrustMerge
