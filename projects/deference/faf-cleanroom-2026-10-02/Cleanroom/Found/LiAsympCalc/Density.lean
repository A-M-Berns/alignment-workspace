import Cleanroom.Found.LiAsympCalc.WeightedAverage

/-!
# C. The density lemma

Target C of [[li-asymp-calc-mandate]]: a `≤ 1` sequence whose Cesàro mean tends to `1` is
`≥ θ` (any `θ < 1`) infinitely often on every set of positive upper density. Only the upper
bound `x ≤ 1` is assumed — no `0 ≤ x` — because the consumer applies it to an expectation of a
`[0,1]` indicator, and the lemma does not need the lower bound. The contrapositive is stated
quantitatively (`cesaro_le_of_lt_on`): if `x < θ` on `S` beyond day `n₀`, the Cesàro mean is
at most `1 - (1-θ)·(countIn S N - n₀)/N`.
-/

namespace Cleanroom.Found.LiAsympCalc

open LogicalInduction Filter Topology Finset

open Classical in
/-- `countIn` as a real-valued indicator sum.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma countIn_eq_sum (S : Set ℕ) (N : ℕ) :
    (countIn S N : ℝ) = ∑ i ∈ range N, (if i ∈ S then (1 : ℝ) else 0) := by
  unfold countIn
  rw [Finset.card_filter]
  push_cast
  rfl

/-- `countIn S N ≤ N`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma countIn_le (S : Set ℕ) (N : ℕ) : countIn S N ≤ N := by
  classical
  unfold countIn
  exact (Finset.card_filter_le _ _).trans (by simp)

open Classical in
/-- Indicator-sum bookkeeping: the count of `S` below `N` is at most the count of
`S ∩ [n₀, ∞)` below `N` plus `n₀`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma countIn_le_sum_tail_add (S : Set ℕ) (N n₀ : ℕ) :
    (countIn S N : ℝ) ≤
      (∑ i ∈ range N, (if i ∈ S ∧ n₀ ≤ i then (1 : ℝ) else 0)) + n₀ := by
  rw [countIn_eq_sum]
  calc ∑ i ∈ range N, (if i ∈ S then (1 : ℝ) else 0)
      ≤ ∑ i ∈ range N, ((if i ∈ S ∧ n₀ ≤ i then (1 : ℝ) else 0) +
          (if i < n₀ then (1 : ℝ) else 0)) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hS : i ∈ S
        · by_cases hn : n₀ ≤ i
          · simp only [hS, hn, and_self, if_true]
            split_ifs <;> norm_num
          · simp [hS, hn, not_le.1 hn]
        · simp only [hS, false_and, if_false, zero_add]
          split_ifs <;> norm_num
    _ = (∑ i ∈ range N, (if i ∈ S ∧ n₀ ≤ i then (1 : ℝ) else 0)) +
          ∑ i ∈ range N, (if i < n₀ then (1 : ℝ) else 0) := Finset.sum_add_distrib
    _ ≤ (∑ i ∈ range N, (if i ∈ S ∧ n₀ ≤ i then (1 : ℝ) else 0)) + n₀ := by
        gcongr
        rw [Finset.sum_boole]
        have hcard : ((range N).filter (fun i => i < n₀)).card ≤ n₀ := by
          calc ((range N).filter (fun i => i < n₀)).card ≤ (range n₀).card :=
                Finset.card_le_card (fun i hi => by
                  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
                  exact hi.2)
            _ = n₀ := Finset.card_range n₀
        exact_mod_cast hcard

/-- **Quantitative contrapositive of the density lemma**: if `x ≤ 1` everywhere and `x < θ` on
`S` from day `n₀` on, then for `0 < N`,
`cesaro x N ≤ 1 - (1 - θ) * (countIn S N - n₀) / N`.
Source: [[li-asymp-calc-mandate]] C1 (contrapositive form)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem cesaro_le_of_lt_on {x : ℕ → ℝ} {S : Set ℕ} {θ : ℝ} (hθ : θ < 1) (hx : ∀ n, x n ≤ 1)
    {n₀ : ℕ} (hlt : ∀ n, n₀ ≤ n → n ∈ S → x n < θ) {N : ℕ} (hN : 0 < N) :
    cesaro x N ≤ 1 - (1 - θ) * ((countIn S N : ℝ) - n₀) / N := by
  classical
  have hθ' : 0 < 1 - θ := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpt : ∀ i, x i ≤ 1 - (1 - θ) * (if i ∈ S ∧ n₀ ≤ i then (1 : ℝ) else 0) := by
    intro i
    split_ifs with h
    · have := hlt i h.2 h.1
      linarith
    · simpa using hx i
  have hsum : ∑ i ∈ range N, x i ≤
      N - (1 - θ) * ∑ i ∈ range N, (if i ∈ S ∧ n₀ ≤ i then (1 : ℝ) else 0) := by
    calc ∑ i ∈ range N, x i
        ≤ ∑ i ∈ range N, (1 - (1 - θ) * (if i ∈ S ∧ n₀ ≤ i then (1 : ℝ) else 0)) :=
          Finset.sum_le_sum (fun i _ => hpt i)
      _ = N - (1 - θ) * ∑ i ∈ range N, (if i ∈ S ∧ n₀ ≤ i then (1 : ℝ) else 0) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            mul_one, Finset.mul_sum]
  have hcount := countIn_le_sum_tail_add S N n₀
  have hC := mul_le_mul_of_nonneg_left hcount hθ'.le
  rw [cesaro, div_le_iff₀ hNR, sub_mul, div_mul_cancel₀ _ hNR.ne']
  linarith

/-- **Density lemma** (C1): for `θ < 1`, `x ≤ 1`, `cesaro x → 1`, and `S` of upper density
`≥ d > 0`: `θ ≤ x n` for infinitely many `n ∈ S`. The `θ = 1/2` case is the sources'.
Source: `lean-deference` `StalenessDensity.lean:46`; [[delay-program]] §6 T3; root-fa-030
Kind: P
Fidelity: stronger: any `θ < 1`, no lower bound on `x`
Hyps: (a) none -/
theorem density_lemma {x : ℕ → ℝ} {S : Set ℕ} {d θ : ℝ} (hθ : θ < 1) (hx : ∀ n, x n ≤ 1)
    (hces : Tendsto (cesaro x) atTop (𝓝 1)) (hS : UpperDensityGE S d) (hd : 0 < d) :
    ∃ᶠ n in atTop, n ∈ S ∧ θ ≤ x n := by
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hcon
  have hlt : ∀ n, n₀ ≤ n → n ∈ S → x n < θ := fun n hn hnS =>
    lt_of_not_ge (fun h => hn₀ n hn ⟨hnS, h⟩)
  have hθ' : 0 < 1 - θ := by linarith
  have h1 : Tendsto (fun N : ℕ => (1 - θ) * n₀ / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hev1 := hces.eventually (lt_mem_nhds (by nlinarith : 1 - (1 - θ) * d / 2 < (1 : ℝ)))
  have hev2 := h1.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < (1 - θ) * d / 2))
  obtain ⟨N, hSN, hN1, hN2, hNpos⟩ :=
    (hS.and_eventually (hev1.and (hev2.and (eventually_gt_atTop 0)))).exists
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hA := cesaro_le_of_lt_on hθ hx hlt hNpos
  rw [div_lt_iff₀ hNR] at hN2
  have hC : (1 - θ) * (d * N) ≤ (1 - θ) * (countIn S N : ℝ) :=
    mul_le_mul_of_nonneg_left hSN hθ'.le
  have hkey : (1 - θ) * ((countIn S N : ℝ) - n₀) / N > (1 - θ) * d / 2 := by
    rw [gt_iff_lt, lt_div_iff₀ hNR]
    nlinarith
  linarith

/-! ### Witness -/

/-- The witness sequence: `0` on day `0`, `1` afterwards. Non-constant; its Cesàro mean
`(N-1)/N` tends to `1`; it is `< 1/2` at `0 ∈ evens`.
Source: [[li-asymp-calc-mandate]] C1
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def densityWitness (n : ℕ) : ℝ := if n = 0 then 0 else 1

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma densityWitness_sum (M : ℕ) : ∑ i ∈ range (M + 1), densityWitness i = M := by
  rw [Finset.sum_range_succ']
  simp [densityWitness]

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma tendsto_cesaro_densityWitness : Tendsto (cesaro densityWitness) atTop (𝓝 1) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  refine (tendsto_natCast_div_add_atTop (1 : ℝ)).congr (fun M => ?_)
  rw [cesaro, densityWitness_sum]
  push_cast
  ring

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma card_filter_even_range (a : ℕ) : ((range (2 * a)).filter Even).card = a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [show 2 * (a + 1) = 2 * a + 1 + 1 by ring, Finset.range_add_one, Finset.range_add_one,
      Finset.filter_insert, Finset.filter_insert, if_neg (by simp),
      if_pos (even_two_mul a), Finset.card_insert_of_notMem (by simp), ih]

/-- `UpperDensityGE S d` is unsatisfiable for `d > 1`: the definition is not junk-permissive at
the top (recorded convention; audit round 1, adversarial probe 2).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem upperDensityGE_gt_one_false (S : Set ℕ) {d : ℝ} (hd : 1 < d) : ¬ UpperDensityGE S d := by
  intro h
  obtain ⟨N, hN, hpos⟩ := (h.and_eventually (eventually_gt_atTop 0)).exists
  have h1 : (countIn S N : ℝ) ≤ N := by exact_mod_cast countIn_le S N
  have hNR : (0 : ℝ) < N := by exact_mod_cast hpos
  nlinarith

/-- `UpperDensityGE S d` holds for every `S` when `d ≤ 0` (recorded convention: `density_lemma`
carries `0 < d` for this reason).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem upperDensityGE_of_nonpos (S : Set ℕ) {d : ℝ} (hd : d ≤ 0) : UpperDensityGE S d :=
  Eventually.frequently (Eventually.of_forall (fun N =>
    (mul_nonpos_of_nonpos_of_nonneg hd (Nat.cast_nonneg N)).trans (Nat.cast_nonneg _)))

/-- The evens have upper density `≥ 1/2` (in fact density `1/2`).
Source: [[li-asymp-calc-mandate]] C1
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem upperDensityGE_evens : UpperDensityGE {n | Even n} (1 / 2) := by
  classical
  unfold UpperDensityGE
  rw [frequently_atTop]
  intro a
  refine ⟨2 * a, by omega, ?_⟩
  have hcount : countIn {n | Even n} (2 * a) = a := by
    unfold countIn
    convert card_filter_even_range a using 3
    simp
  rw [hcount]
  push_cast
  linarith

/-- **Density witness (N−, one exception)**: the full hypothesis package of `density_lemma` at
`θ = 1/2`, `S = evens`, `d = 1/2`, with `x = densityWitness`, which is `< 1/2` at `0 ∈ S` only.
Graded N− because `x` is eventually constant: `1/2 ≤ x n` holds for every `n ≥ 1`, so the
conclusion's "infinitely often on `S`" is instantiated for the stronger reason "eventually on
`S`", and this witness cannot tell `∃ᶠ` from `∀ᶠ`. The N+ witness, with infinitely many
density-zero exceptions on `S`, is `density_witness_squares` (`Spikes.lean`).
Source: [[li-asymp-calc-mandate]] C1
Kind: N-
Fidelity: n/a
Hyps: n/a -/
theorem density_witness :
    ((1 : ℝ) / 2 < 1) ∧ (∀ n, densityWitness n ≤ 1) ∧
      Tendsto (cesaro densityWitness) atTop (𝓝 1) ∧
      UpperDensityGE {n | Even n} (1 / 2) ∧ ((0 : ℝ) < 1 / 2) ∧
      (∃ n, n ∈ {n | Even n} ∧ densityWitness n < 1 / 2) ∧
      (∃ᶠ n in atTop, n ∈ {n | Even n} ∧ (1 / 2 : ℝ) ≤ densityWitness n) := by
  refine ⟨by norm_num, fun n => ?_, tendsto_cesaro_densityWitness, upperDensityGE_evens,
    by norm_num, ⟨0, by simp, by simp [densityWitness]⟩, ?_⟩
  · unfold densityWitness
    split_ifs <;> norm_num
  · exact density_lemma (by norm_num) (fun n => by unfold densityWitness; split_ifs <;> norm_num)
      tendsto_cesaro_densityWitness upperDensityGE_evens (by norm_num)

end Cleanroom.Found.LiAsympCalc
