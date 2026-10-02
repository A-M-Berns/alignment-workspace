import Cleanroom.Deference.DefDoseResponse.Coin
import Mathlib.Analysis.PSeries

/-!
# Audit r3 (adversarial) probe — the predictability hypothesis of `nmart_tendsto_ae` is load-bearing

`Coin.lean`'s `nmart_tendsto_ae` takes two hypotheses on the weight process `w`: the `[0,1]` bound
`hw` (whose necessity the package records at `altWeight`) and the predictability `hc` — `w x n`
reads the coins `< n` only. The mandate's trap (i) asserts that without the delay (the builder
reading the day's own coin) "the theorem is false", and the package keeps the delay hypothesis on
that ground; through rounds 0–2 nothing machine-checked it. This probe does: at the omniscient
weight `w x n := 𝟙[x n]` (`[0,1]`-valued, reads the day's coin) and `p ∈ (0,1)`, the normalized
sums are `(1 − p)·∑_{j < T_N} 1/(j+2)` with `T_N` the number of trues up to `N`, which diverges on
every coin with infinitely many trues — a set of full measure (the coins eventually `false` from
day `m` on lie in every cylinder of mass `(1−p)^K`). So the `hc`-free statement is **false**
(`predictability_load_bearing`), and `nmart_tendsto_ae`'s two hypotheses are each necessary.
Positive by-product: `nmart_tendsto_ae` at `w ≡ 1` is the classical a.s. convergence of
`∑_{k≤N} (𝟙[x k] − p)/(k + 2)` (`nmart_const_one_tendsto_ae`). Not imported by the library.
-/

namespace Cleanroom.Deference.DefDoseResponse.AuditR3

open LogicalInduction Cleanroom.Li.LiPseudorandom Cleanroom.Found.LiAsympCalc MeasureTheory
  ProbabilityTheory Cleanroom.Deference.DefDoseResponse
open Filter Topology
open scoped ENNReal NNReal

/-! ## Positive sanity instance: the constant weight -/

/-- `nmart_tendsto_ae` at `w ≡ 1`: a.s. `∑_{k≤N} (𝟙[x k] − p)/(k + 2)` converges — the theorem's
simplest instance has the classical content. -/
theorem nmart_const_one_tendsto_ae (p : unitInterval) :
    ∀ᵐ x ∂(coinMeasure p), ∃ L : ℝ,
      Tendsto (fun N => prefixSum (fun k => (truthR x k - p) / ((k : ℝ) + 2)) N) atTop (𝓝 L) := by
  have h := nmart_tendsto_ae p (w := fun _ _ => (1 : ℝ)) (fun _ _ => ⟨zero_le_one, le_rfl⟩)
    (fun _ _ _ _ => rfl)
  refine h.mono fun x ⟨L, hL⟩ => ⟨L, ?_⟩
  refine hL.congr fun N => ?_
  unfold nmart
  congr 1
  funext k
  unfold nincr
  have hps : prefixSum (fun _ => (1 : ℝ)) k = (k : ℝ) + 1 := by
    induction k with
    | zero => simp
    | succ k ih => rw [prefixSum_succ, ih]; push_cast; ring
  rw [hps]
  ring

/-! ## The omniscient weight -/

/-- The omniscient weight process: the day's own coin. `[0,1]`-valued; reads `x n`, so it is not
predictable. -/
noncomputable def omniW (x : ℕ → Bool) : ℕ → ℝ := truthR x

theorem omniW_mem (x : ℕ → Bool) (n : ℕ) : 0 ≤ omniW x n ∧ omniW x n ≤ 1 := by
  unfold omniW truthR
  split_ifs <;> norm_num

/-- The number of trues among the coins `0, …, N`. -/
def cnt (x : ℕ → Bool) (N : ℕ) : ℕ := ((Finset.range (N + 1)).filter fun k => x k = true).card

theorem cnt_zero (x : ℕ → Bool) : cnt x 0 = if x 0 = true then 1 else 0 := by
  unfold cnt
  rw [zero_add, Finset.range_one, Finset.filter_singleton]
  split_ifs <;> simp

theorem cnt_succ (x : ℕ → Bool) (N : ℕ) :
    cnt x (N + 1) = cnt x N + if x (N + 1) = true then 1 else 0 := by
  unfold cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · have hnot : N + 1 ∉ (Finset.range (N + 1)).filter fun k => x k = true := by simp
    rw [Finset.card_insert_of_notMem hnot]
  · simp

theorem cnt_mono (x : ℕ → Bool) : Monotone (cnt x) := by
  intro a b hab
  unfold cnt
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro i hi
  rw [Finset.mem_range] at hi ⊢
  omega

theorem prefixSum_truthR (x : ℕ → Bool) (N : ℕ) : prefixSum (truthR x) N = (cnt x N : ℝ) := by
  induction N with
  | zero =>
    rw [prefixSum_zero, cnt_zero]
    unfold truthR
    split_ifs <;> simp
  | succ N ih =>
    rw [prefixSum_succ, ih, cnt_succ]
    unfold truthR
    split_ifs <;> push_cast <;> ring

/-- `H m := ∑_{j < m} 1/(j + 2)`. -/
noncomputable def H (m : ℕ) : ℝ := ∑ j ∈ Finset.range m, (1 / ((j : ℝ) + 2))

theorem H_succ (m : ℕ) : H (m + 1) = H m + 1 / ((m : ℝ) + 2) := by
  unfold H
  rw [Finset.sum_range_succ]

theorem H_tendsto : Tendsto H atTop atTop := by
  have h1 : Tendsto (fun m => (1 / 2 : ℝ) * ∑ j ∈ Finset.range m, (1 / ((j : ℝ) + 1)))
      atTop atTop :=
    Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono (fun m => ?_) h1
  unfold H
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  calc (1 / 2 : ℝ) * (1 / ((j : ℝ) + 1)) = 1 / (2 * ((j : ℝ) + 1)) := by
        rw [div_mul_div_comm, one_mul]
    _ ≤ 1 / ((j : ℝ) + 2) := one_div_le_one_div_of_le (by positivity) (by linarith)

/-- At the omniscient weight the normalized martingale is `(1 − p) · H(T_N)`. -/
theorem nmart_omni (p : unitInterval) (x : ℕ → Bool) (N : ℕ) :
    nmart p omniW N x = (1 - (p : ℝ)) * H (cnt x N) := by
  induction N with
  | zero =>
    unfold nmart
    rw [prefixSum_zero]
    unfold nincr omniW
    rw [prefixSum_zero, cnt_zero]
    unfold truthR
    split_ifs <;> simp [H] <;> ring
  | succ N ih =>
    unfold nmart at ih ⊢
    rw [prefixSum_succ, ih]
    unfold nincr omniW
    rw [prefixSum_truthR, cnt_succ]
    unfold truthR
    split_ifs with h
    · rw [H_succ]
      push_cast
      field_simp
      ring
    · simp

/-- On a coin with `T_N → ∞` and `p < 1`, the normalized sums have no finite limit. -/
theorem nmart_omni_no_limit (p : unitInterval) (hp1 : (p : ℝ) < 1) (x : ℕ → Bool)
    (hx : Tendsto (cnt x) atTop atTop) :
    ¬ ∃ L : ℝ, Tendsto (fun N => nmart p omniW N x) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hdiv : Tendsto (fun N => nmart p omniW N x) atTop atTop := by
    simp_rw [nmart_omni]
    exact (H_tendsto.comp hx).const_mul_atTop (by linarith)
  have h1 := hdiv.eventually (eventually_gt_atTop (L + 1))
  have h2 := hL.eventually (Metric.ball_mem_nhds L one_pos)
  obtain ⟨N, hN1, hN2⟩ := (h1.and h2).exists
  rw [Real.dist_eq] at hN2
  have := abs_lt.mp hN2
  linarith

/-- Infinitely many trues ⟹ `T_N → ∞`. -/
theorem cnt_tendsto_of_frequently (x : ℕ → Bool) (hx : ∀ m, ∃ n, m ≤ n ∧ x n = true) :
    Tendsto (cnt x) atTop atTop := by
  refine tendsto_atTop_atTop_of_monotone (cnt_mono x) fun b => ?_
  induction b with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ b ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨n, hn, hxn⟩ := hx (N + 1)
    refine ⟨n, ?_⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [cnt_succ, if_pos hxn]
    have := cnt_mono x (show N ≤ n' by omega)
    omega

/-! ## The coins eventually `false` form a null set -/

/-- The coins that are `false` from day `m` on. -/
def evFalse (m : ℕ) : Set (ℕ → Bool) := {x | ∀ n, m ≤ n → x n = false}

theorem evFalse_subset_cyl (m K : ℕ) :
    evFalse m ⊆ Set.pi (↑(Finset.Ico m (m + K)) : Set ℕ) (fun _ => ({false} : Set Bool)) := by
  intro x hx i hi
  rw [Finset.coe_Ico, Set.mem_Ico] at hi
  rw [Set.mem_singleton_iff]
  exact hx i hi.1

theorem coinMeasure_evFalse_le (p : unitInterval) (m K : ℕ) :
    coinMeasure p (evFalse m) ≤
      ((unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞)) ^ K := by
  refine (measure_mono (evFalse_subset_cyl m K)).trans ?_
  unfold coinMeasure
  rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _), Finset.prod_const,
    Nat.card_Ico, Nat.add_sub_cancel_left,
    bernoulliMeasure_apply_of_notMem_of_mem p (measurableSet_singleton _) (by simp)
      (Set.mem_singleton _)]

theorem symm_lt_one (p : unitInterval) (hp0 : 0 < (p : ℝ)) :
    ((unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞)) < 1 := by
  rw [ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_coe, unitInterval.coe_toNNReal, NNReal.coe_one,
    unitInterval.coe_symm_eq]
  linarith

theorem coinMeasure_evFalse_null (p : unitInterval) (hp0 : 0 < (p : ℝ)) (m : ℕ) :
    coinMeasure p (evFalse m) = 0 := by
  have ht := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (symm_lt_one p hp0)
  exact nonpos_iff_eq_zero.mp (ge_of_tendsto' ht fun K => coinMeasure_evFalse_le p m K)

/-- For `p > 0`, almost every coin has infinitely many trues. -/
theorem ae_cnt_tendsto (p : unitInterval) (hp0 : 0 < (p : ℝ)) :
    ∀ᵐ x ∂(coinMeasure p), Tendsto (cnt x) atTop atTop := by
  have hnull : coinMeasure p (⋃ m, evFalse m) = 0 :=
    measure_iUnion_null fun m => coinMeasure_evFalse_null p hp0 m
  rw [measure_eq_zero_iff_ae_notMem] at hnull
  refine hnull.mono fun x hx => ?_
  rw [Set.mem_iUnion] at hx
  refine cnt_tendsto_of_frequently x fun m => ?_
  by_contra hcon
  apply hx
  refine ⟨m, ?_⟩
  show ∀ n, m ≤ n → x n = false
  intro n hn
  have hne : ¬ x n = true := fun ht => hcon ⟨n, hn, ht⟩
  simpa using hne

/-! ## The refutation -/

/-- At the omniscient weight and `p ∈ (0,1)`, the conclusion of `nmart_tendsto_ae` fails. -/
theorem nmart_omni_not_tendsto_ae (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ¬ ∀ᵐ x ∂(coinMeasure p), ∃ L : ℝ, Tendsto (fun N => nmart p omniW N x) atTop (𝓝 L) := by
  intro h
  have h' : ∀ᵐ x ∂(coinMeasure p),
      ¬ ∃ L : ℝ, Tendsto (fun N => nmart p omniW N x) atTop (𝓝 L) :=
    (ae_cnt_tendsto p hp0).mono fun x hx => nmart_omni_no_limit p hp1 x hx
  obtain ⟨x, h1, h2⟩ := coinMeasure_ae_exists p (h.and h')
  exact h2 h1

/-- `½` as a point of the unit interval. -/
noncomputable def pHalf : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

/-- **The predictability hypothesis is load-bearing**: `nmart_tendsto_ae` with `hc` dropped is
false (at `p = ½` and the omniscient `[0,1]`-valued weight). No `sorry`. -/
theorem predictability_load_bearing :
    ¬ ∀ (p : unitInterval) (w : (ℕ → Bool) → ℕ → ℝ), (∀ x n, 0 ≤ w x n ∧ w x n ≤ 1) →
      ∀ᵐ x ∂(coinMeasure p), ∃ L : ℝ, Tendsto (fun N => nmart p w N x) atTop (𝓝 L) := fun h =>
  nmart_omni_not_tendsto_ae pHalf (by show (0 : ℝ) < 1 / 2; norm_num)
    (by show (1 / 2 : ℝ) < 1; norm_num) (h pHalf omniW omniW_mem)

end Cleanroom.Deference.DefDoseResponse.AuditR3
