import Cleanroom.Found.LiAsympCalc.WeightedAverage
import Cleanroom.Found.LiAsympCalc.LimitPoint
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# F. The log-budget lemma

Target F of [[li-asymp-calc-mandate]] (root-fa-2-004, [[fa-positive-results-corrected-v3]] §3).

* F1: `x - x² ≤ log (1 + x)` for `-1/2 ≤ x`, by monotonicity of `log (1+x) - x + x²` on
  `[-1/2, 0]` (antitone) and `[0, ∞)` (monotone), from the sign of its derivative
  `x (1 + 2x) / (1 + x)`.
* F2: for `λ ∈ (0, 1/2]`, `w k ∈ [0,1]`, `Δ k ∈ [-1,1]`, each factor `1 + λ w k Δ k ∈ [1/2, 3/2]`,
  the product is positive, and `log ∏ ≥ λ ∑ w Δ - λ² ∑ w`. Corollary in **exploitation shape**:
  with divergent `∑ w`, `0 < λ < ε`, and `ε ∑ w ≤ ∑ w Δ` **frequently** (a limit point suffices,
  no full limit), the log-product is frequently above every bound, while every factor keeps
  each partial product and each mid-window value `b (1 + λ w (x - e))` at least half the
  previous one. v3's constants; not `StreamlinedSS.lean`'s `η < 1/4`, `4η²`.
-/

namespace Cleanroom.Found.LiAsympCalc

open LogicalInduction Filter Topology Finset

/-! ### F1 -/

/-- `log (1 + x) - x + x²`, the function whose sign is F1.
Source: root-fa-2-004
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def logBudgetAux (x : ℝ) : ℝ := Real.log (1 + x) - x + x ^ 2

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma logBudgetAux_zero : logBudgetAux 0 = 0 := by
  simp [logBudgetAux]

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma logBudgetAux_hasDerivAt {x : ℝ} (hx : -1 < x) :
    HasDerivAt logBudgetAux (1 / (1 + x) - 1 + 2 * x) x := by
  have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id' x).const_add 1
  have hlog : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x :=
    h1.log (by linarith)
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have := (hlog.sub (hasDerivAt_id' x)).add hsq
  unfold logBudgetAux
  exact this

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma logBudgetAux_deriv_eq {x : ℝ} (hx : -1 < x) :
    deriv logBudgetAux x = x * (1 + 2 * x) / (1 + x) := by
  rw [(logBudgetAux_hasDerivAt hx).deriv]
  have h1 : (1 : ℝ) + x ≠ 0 := by linarith
  field_simp
  ring

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma logBudgetAux_nonneg_of_nonpos {x : ℝ} (hx1 : -1 / 2 ≤ x) (hx2 : x ≤ 0) :
    0 ≤ logBudgetAux x := by
  have hanti : AntitoneOn logBudgetAux (Set.Icc (-1 / 2) 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · intro y hy
      exact (logBudgetAux_hasDerivAt (by linarith [hy.1])).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact (logBudgetAux_hasDerivAt (by linarith [hy.1])).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [logBudgetAux_deriv_eq (by linarith [hy.1])]
      apply div_nonpos_of_nonpos_of_nonneg
      · nlinarith [hy.1, hy.2]
      · linarith [hy.1]
  have := hanti (Set.mem_Icc.2 ⟨hx1, hx2⟩) (Set.mem_Icc.2 ⟨by norm_num, le_rfl⟩) hx2
  rw [logBudgetAux_zero] at this
  exact this

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma logBudgetAux_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ logBudgetAux x := by
  have hmono : MonotoneOn logBudgetAux (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · intro y hy
      exact (logBudgetAux_hasDerivAt (by linarith [Set.mem_Ici.1 hy])).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact (logBudgetAux_hasDerivAt (by linarith [Set.mem_Ioi.1 hy])).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy' := Set.mem_Ioi.1 hy
      rw [logBudgetAux_deriv_eq (by linarith)]
      apply div_nonneg
      · nlinarith
      · linarith
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  rw [logBudgetAux_zero] at this
  exact this

/-- **F1**: `x - x² ≤ log (1 + x)` for `-1/2 ≤ x`.
Source: root-fa-2-004; [[fa-positive-results-corrected-v3]] §3; `StreamlinedSS.lean:253`
(which does `|x| ≤ 1/2`)
Kind: P
Fidelity: stronger: one-sided hypothesis `-1/2 ≤ x` (no upper bound)
Hyps: (a) none -/
theorem sub_sq_le_log_one_add {x : ℝ} (hx : -1 / 2 ≤ x) : x - x ^ 2 ≤ Real.log (1 + x) := by
  rcases le_total x 0 with h | h
  · have := logBudgetAux_nonneg_of_nonpos hx h
    unfold logBudgetAux at this
    linarith
  · have := logBudgetAux_nonneg_of_nonneg h
    unfold logBudgetAux at this
    linarith

/-! ### F2 -/

/-- Each budget factor lies in `[1/2, 3/2]`.
Source: [[fa-positive-results-corrected-v3]] §3 lines 61–63
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem budgetFactor_mem {l w Δ : ℝ} (hl0 : 0 < l) (hl : l ≤ 1 / 2) (hw0 : 0 ≤ w)
    (hw1 : w ≤ 1) (hΔ : |Δ| ≤ 1) :
    1 / 2 ≤ 1 + l * w * Δ ∧ 1 + l * w * Δ ≤ 3 / 2 := by
  have h := abs_le.1 hΔ
  have hlw0 : 0 ≤ l * w := mul_nonneg hl0.le hw0
  have hlw : l * w ≤ 1 / 2 := by nlinarith
  have h1 : -(l * w) ≤ l * w * Δ := by nlinarith
  have h2 : l * w * Δ ≤ l * w := by nlinarith
  constructor <;> linarith

/-- Per-factor log bound: `log (1 + λ w Δ) ≥ λ w Δ - λ² w`.
Source: [[fa-positive-results-corrected-v3]] §3 lines 61–63
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem log_budgetFactor_ge {l w Δ : ℝ} (hl0 : 0 < l) (hl : l ≤ 1 / 2) (hw0 : 0 ≤ w)
    (hw1 : w ≤ 1) (hΔ : |Δ| ≤ 1) :
    l * w * Δ - l ^ 2 * w ≤ Real.log (1 + l * w * Δ) := by
  have hmem := budgetFactor_mem hl0 hl hw0 hw1 hΔ
  have hF1 := sub_sq_le_log_one_add (x := l * w * Δ) (by linarith [hmem.1])
  have hΔ2 : Δ ^ 2 ≤ 1 := by
    have := abs_le.1 hΔ
    nlinarith
  have hx2 : (l * w * Δ) ^ 2 ≤ l ^ 2 * w := by
    have h1 : (l * w * Δ) ^ 2 = l ^ 2 * w * (w * Δ ^ 2) := by ring
    rw [h1]
    have h2 : w * Δ ^ 2 ≤ 1 := by
      calc w * Δ ^ 2 ≤ w * 1 := mul_le_mul_of_nonneg_left hΔ2 hw0
        _ ≤ 1 := by linarith
    have h3 : 0 ≤ l ^ 2 * w := by positivity
    calc l ^ 2 * w * (w * Δ ^ 2) ≤ l ^ 2 * w * 1 := mul_le_mul_of_nonneg_left h2 h3
      _ = l ^ 2 * w := mul_one _
  linarith

/-- The budget product over `range (K+1)` is positive.
Source: [[fa-positive-results-corrected-v3]] §3
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem budgetProd_pos {l : ℝ} {w Δ : ℕ → ℝ} (hl0 : 0 < l) (hl : l ≤ 1 / 2)
    (hw : ∀ k, w k ∈ Set.Icc (0 : ℝ) 1) (hΔ : ∀ k, |Δ k| ≤ 1) (K : ℕ) :
    0 < ∏ k ∈ range (K + 1), (1 + l * w k * Δ k) :=
  Finset.prod_pos (fun k _ => by
    linarith [(budgetFactor_mem hl0 hl (hw k).1 (hw k).2 (hΔ k)).1])

/-- **F2**: `log ∏_{k ≤ K} (1 + λ w_k Δ_k) ≥ λ ∑_{k ≤ K} w_k Δ_k - λ² ∑_{k ≤ K} w_k`.
Source: [[fa-positive-results-corrected-v3]] §3 lines 61–63; root-fa-2-004
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem log_budgetProd_ge {l : ℝ} {w Δ : ℕ → ℝ} (hl0 : 0 < l) (hl : l ≤ 1 / 2)
    (hw : ∀ k, w k ∈ Set.Icc (0 : ℝ) 1) (hΔ : ∀ k, |Δ k| ≤ 1) (K : ℕ) :
    l * (∑ k ∈ range (K + 1), w k * Δ k) - l ^ 2 * ∑ k ∈ range (K + 1), w k ≤
      Real.log (∏ k ∈ range (K + 1), (1 + l * w k * Δ k)) := by
  rw [Real.log_prod (fun k _ => by
    linarith [(budgetFactor_mem hl0 hl (hw k).1 (hw k).2 (hΔ k)).1] :
      ∀ k ∈ range (K + 1), 1 + l * w k * Δ k ≠ 0)]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro k _
  have := log_budgetFactor_ge hl0 hl (hw k).1 (hw k).2 (hΔ k)
  linarith [show l * (w k * Δ k) = l * w k * Δ k by ring]

/-- Mid-window value: for `b > 0`, `x e ∈ [0,1]`, `b (1 + λ w (x - e)) ≥ b / 2 > 0`.
Source: [[fa-positive-results-corrected-v3]] §3
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem midWindow_ge_half {b l w x e : ℝ} (hb : 0 < b) (hl0 : 0 < l) (hl : l ≤ 1 / 2)
    (hw : w ∈ Set.Icc (0 : ℝ) 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) (he : e ∈ Set.Icc (0 : ℝ) 1) :
    b / 2 ≤ b * (1 + l * w * (x - e)) ∧ 0 < b * (1 + l * w * (x - e)) := by
  have hΔ : |x - e| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2, he.1, he.2]
  have hmem := budgetFactor_mem hl0 hl hw.1 hw.2 hΔ
  constructor
  · nlinarith [hmem.1]
  · exact mul_pos hb (by linarith [hmem.1])

/-- **Exploitation shape** (F2 corollary): divergent `∑ w`, `0 < λ < ε`, `λ ≤ 1/2`, and
`ε · ∑_{k≤K} w_k ≤ ∑_{k≤K} w_k Δ_k` **frequently** ⟹ the log-product is frequently above
every bound `M`. Stated with `∃ᶠ`, not a full limit: limit-point unbiasedness suffices. The
`o(1)` of v3's `(λ(ε - o(1)) - λ²) W` is absorbed into `ε` (a dependent shrinks `ε`). A
composition of `log_budgetProd_ge` (the `P`) with divergence and the frequent-excess hypothesis.
Source: [[fa-positive-results-corrected-v3]] §3; root-fa-2-004
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem log_budgetProd_frequently_ge {l ε : ℝ} {w Δ : ℕ → ℝ}
    (hw : ∀ k, w k ∈ Set.Icc (0 : ℝ) 1) (hΔ : ∀ k, |Δ k| ≤ 1)
    (hdiv : Tendsto (prefixSum w) atTop atTop) (hl0 : 0 < l) (hl : l ≤ 1 / 2) (hlε : l < ε)
    (hfreq : ∃ᶠ K in atTop, ε * prefixSum w K ≤ prefixSum (fun k => w k * Δ k) K) :
    ∀ M : ℝ, ∃ᶠ K in atTop, M ≤ Real.log (∏ k ∈ range (K + 1), (1 + l * w k * Δ k)) := by
  intro M
  have hgrow : Tendsto (fun K => l * (ε - l) * prefixSum w K) atTop atTop :=
    hdiv.const_mul_atTop (by nlinarith)
  have hev := hgrow.eventually (eventually_ge_atTop M)
  refine (hfreq.and_eventually hev).mono (fun K hK => ?_)
  obtain ⟨hK, hM⟩ := hK
  have hlog := log_budgetProd_ge hl0 hl hw hΔ K
  have hP := prefixSum_nonneg (fun k => (hw k).1) K
  calc M ≤ l * (ε - l) * prefixSum w K := hM
    _ = l * (ε * prefixSum w K) - l ^ 2 * prefixSum w K := by ring
    _ ≤ l * prefixSum (fun k => w k * Δ k) K - l ^ 2 * prefixSum w K := by
        have := mul_le_mul_of_nonneg_left hK hl0.le
        linarith
    _ ≤ Real.log (∏ k ∈ range (K + 1), (1 + l * w k * Δ k)) := hlog

/-! ### Witness -/

/-- Witness weighting: `1/2` on day `0`, `1` afterwards (non-constant, `[0,1]`, divergent).
Source: [[li-asymp-calc-mandate]] F2
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def budgetW (k : ℕ) : ℝ := if k = 0 then 1 / 2 else 1

/-- Witness excess stream: `1` on even days, `1/2` on odd days (non-constant, `[-1,1]`).
Source: [[li-asymp-calc-mandate]] F2
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def budgetΔ (k : ℕ) : ℝ := if Even k then 1 else 1 / 2

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma budgetW_mem (k : ℕ) : budgetW k ∈ Set.Icc (0 : ℝ) 1 := by
  unfold budgetW
  split_ifs <;> constructor <;> norm_num

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma budgetΔ_abs_le (k : ℕ) : |budgetΔ k| ≤ 1 := by
  unfold budgetΔ
  split_ifs <;> norm_num

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma half_le_budgetW (k : ℕ) : 1 / 2 ≤ budgetW k := by
  unfold budgetW
  split_ifs <;> norm_num

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma half_le_budgetΔ (k : ℕ) : 1 / 2 ≤ budgetΔ k := by
  unfold budgetΔ
  split_ifs <;> norm_num

/-- **F2 witness (N+, everyday excess)**: non-constant `w`, `Δ` with divergent mass and the
frequent-excess hypothesis at `ε = 1/2` — in fact on every day, so this witness exercises `∃ᶠ`
as `∀`; the witness that exercises "frequently but not eventually" is `logBudget_witness_sparse`
below. `λ = 1/4 < ε`.
Source: [[li-asymp-calc-mandate]] F2
Kind: N+
Fidelity: n/a
Hyps: n/a -/
theorem logBudget_witness :
    (∀ k, budgetW k ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ k, |budgetΔ k| ≤ 1) ∧
      Tendsto (prefixSum budgetW) atTop atTop ∧
      ((0 : ℝ) < 1 / 4 ∧ (1 / 4 : ℝ) ≤ 1 / 2 ∧ (1 / 4 : ℝ) < 1 / 2) ∧
      (∃ᶠ K in atTop, (1 / 2 : ℝ) * prefixSum budgetW K ≤
        prefixSum (fun k => budgetW k * budgetΔ k) K) ∧
      budgetW 0 ≠ budgetW 1 ∧ budgetΔ 0 ≠ budgetΔ 1 ∧
      ∀ M : ℝ, ∃ᶠ K in atTop,
        M ≤ Real.log (∏ k ∈ range (K + 1), (1 + 1 / 4 * budgetW k * budgetΔ k)) := by
  have hdiv : Tendsto (prefixSum budgetW) atTop atTop := by
    have hlow : ∀ K : ℕ, ((K : ℝ) + 1) / 2 ≤ prefixSum budgetW K := by
      intro K
      have : ∑ _k ∈ range (K + 1), (1 / 2 : ℝ) ≤ ∑ k ∈ range (K + 1), budgetW k :=
        Finset.sum_le_sum (fun k _ => half_le_budgetW k)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
      push_cast at this
      unfold prefixSum
      linarith
    exact tendsto_atTop_mono hlow
      ((tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_div_const
        (by norm_num))
  have hfreq : ∃ᶠ K in atTop, (1 / 2 : ℝ) * prefixSum budgetW K ≤
      prefixSum (fun k => budgetW k * budgetΔ k) K := by
    refine Eventually.frequently (Eventually.of_forall (fun K => ?_))
    unfold prefixSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    have := half_le_budgetΔ k
    have := (budgetW_mem k).1
    nlinarith
  refine ⟨budgetW_mem, budgetΔ_abs_le, hdiv, ⟨by norm_num, by norm_num, by norm_num⟩, hfreq,
    by simp [budgetW], by simp [budgetΔ], ?_⟩
  exact log_budgetProd_frequently_ge budgetW_mem budgetΔ_abs_le hdiv (by norm_num) (by norm_num)
    (by norm_num) hfreq

/-! ### Witness with sparse excess: frequently, not eventually -/

/-- Sparse excess stream: `+1` on the days whose `log₂` is even, `-1` on the others
(`2 · clusterSeq − 1`): long stretches of adverse `Δ`, with the excess condition holding only
along the subsequence `K = 2·4^j − 1` and failing along `K = 4^j − 1`.
Source: [[li-asymp-calc-mandate]] F2; audit round 1, adversarial N6
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def sparseΔ (k : ℕ) : ℝ := 2 * clusterSeq k - 1

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma sparseΔ_abs_le (k : ℕ) : |sparseΔ k| ≤ 1 := by
  unfold sparseΔ
  rcases clusterSeq_mem k with h | h <;> rw [h] <;> norm_num

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma sparseΔ_two : sparseΔ 2 = -1 := by
  have h : Nat.log 2 2 = 1 := by
    have := Nat.log_pow (b := 2) (by norm_num) 1
    rwa [pow_one] at this
  norm_num [sparseΔ, clusterSeq, h]

/-- Supporting lemma (a proof step, not a headline): the uniform prefix sum of `sparseΔ` in
terms of the cluster count.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma prefixSum_sparseΔ (K : ℕ) :
    prefixSum (fun k => (fun _ : ℕ => (1 : ℝ)) k * sparseΔ k) K =
      2 * (∑ i ∈ range (K + 1), clusterSeq i) - ((K : ℝ) + 1) := by
  unfold prefixSum sparseΔ
  simp only [one_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum]
  push_cast
  ring

/-- **F2 witness (N+, sparse excess)**: with the uniform weighting and `Δ = sparseΔ`
(`|Δ| ≤ 1`, non-constant: `Δ 0 = 1`, `Δ 2 = −1`), the frequent-excess hypothesis at
`ε = 1/4` holds along `K = 2·4^j − 1` (where the cluster frequency is `≥ 2/3`) and **fails**
along `K = 4^j − 1` (frequency `≤ 3/8`): it is `∃ᶠ` and not `∀ᶠ`, so the corollary's
"limit-point unbiasedness suffices" is exercised as stated. `λ = 1/8 < ε`; the unbounded-log
conclusion is instantiated through `log_budgetProd_frequently_ge`.
Source: [[li-asymp-calc-mandate]] F2; audit round 1, adversarial N6
Kind: N+
Fidelity: n/a
Hyps: n/a -/
theorem logBudget_witness_sparse :
    (∀ k, (fun _ : ℕ => (1 : ℝ)) k ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ k, |sparseΔ k| ≤ 1) ∧
      Tendsto (prefixSum (fun _ : ℕ => (1 : ℝ))) atTop atTop ∧
      (sparseΔ 0 = 1 ∧ sparseΔ 2 = -1) ∧
      (∃ᶠ K in atTop, (1 / 4 : ℝ) * prefixSum (fun _ : ℕ => (1 : ℝ)) K ≤
        prefixSum (fun k => (fun _ : ℕ => (1 : ℝ)) k * sparseΔ k) K) ∧
      (∃ᶠ K in atTop, ¬ ((1 / 4 : ℝ) * prefixSum (fun _ : ℕ => (1 : ℝ)) K ≤
        prefixSum (fun k => (fun _ : ℕ => (1 : ℝ)) k * sparseΔ k) K)) ∧
      ∀ M : ℝ, ∃ᶠ K in atTop,
        M ≤ Real.log (∏ k ∈ range (K + 1), (1 + 1 / 8 * (fun _ : ℕ => (1 : ℝ)) k * sparseΔ k)) := by
  have hw : ∀ k, (fun _ : ℕ => (1 : ℝ)) k ∈ Set.Icc (0 : ℝ) 1 := fun _ => ⟨zero_le_one, le_rfl⟩
  have hfreq : ∃ᶠ K in atTop, (1 / 4 : ℝ) * prefixSum (fun _ : ℕ => (1 : ℝ)) K ≤
      prefixSum (fun k => (fun _ : ℕ => (1 : ℝ)) k * sparseΔ k) K := by
    rw [frequently_atTop]
    intro a
    refine ⟨2 * 4 ^ a - 1, ?_, ?_⟩
    · have hx := le_four_pow a
      generalize 4 ^ a = x at hx ⊢
      omega
    · rw [prefixSum_one, prefixSum_sparseΔ]
      have hodd := clusterSeq_avg_odd a
      rw [weightedAverage_one] at hodd
      have hK : ((2 * 4 ^ a - 1 : ℕ) : ℝ) + 1 = 2 * 4 ^ a := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (by positivity))]
        push_cast
        ring
      rw [hK] at hodd ⊢
      rw [le_div_iff₀ (by positivity)] at hodd
      have : (0 : ℝ) < 4 ^ a := by positivity
      linarith
  have hnot : ∃ᶠ K in atTop, ¬ ((1 / 4 : ℝ) * prefixSum (fun _ : ℕ => (1 : ℝ)) K ≤
      prefixSum (fun k => (fun _ : ℕ => (1 : ℝ)) k * sparseΔ k) K) := by
    rw [frequently_atTop]
    intro a
    refine ⟨4 ^ (a + 2) - 1, ?_, ?_⟩
    · have hx := le_four_pow (a + 2)
      generalize 4 ^ (a + 2) = x at hx ⊢
      omega
    · rw [prefixSum_one, prefixSum_sparseΔ, not_le]
      have hev := clusterSeq_avg_even (a + 2) (by omega)
      rw [weightedAverage_one] at hev
      have hK : ((4 ^ (a + 2) - 1 : ℕ) : ℝ) + 1 = 4 ^ (a + 2) := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (by positivity))]
        push_cast
        ring
      rw [hK] at hev ⊢
      rw [div_le_iff₀ (by positivity)] at hev
      have : (0 : ℝ) < 4 ^ (a + 2) := by positivity
      linarith
  refine ⟨hw, sparseΔ_abs_le, tendsto_prefixSum_one, ⟨by norm_num [sparseΔ, clusterSeq], sparseΔ_two⟩,
    hfreq, hnot, ?_⟩
  exact log_budgetProd_frequently_ge hw sparseΔ_abs_le tendsto_prefixSum_one (by norm_num)
    (by norm_num) (by norm_num) hfreq

end Cleanroom.Found.LiAsympCalc
