import Cleanroom.Deference.DefObstruction.Witness
import Cleanroom.Found.LiAsympCalc.LimitPoint
import Cleanroom.Found.LiAsympCalc.WeightedAverage
import Cleanroom.Found.LiAsympCalc.Ramp

/-!
# `def-obstruction` · TwoFaces: pointwise-wrong yet aggregate-unbiased, realized (T5)

**(i) The realized two-faces witness.** On the alternating pair (`Witness.lean`), the pointwise
credence defect tends to `1` (`altPair_defect_tendsto_one`) while the uniform-weight bias between
the quote and the reader's deferred credence tends to `0` (`altPair_weightedBias_tendsto_zero`;
FAF's `weightedBias` at the constant weighting `1`). The earlier witness
(lean-deference-028: `a ≡ ½`, `Y` alternating) decoupled forecast from settlement; here the
coupling is through FAF's real inductor over the real ledger, and the settlement alternates
*because the quote does* (findings F-Witness028).

**(ii) Both faces can die.** On the constant best response `aHalf ≡ ½` the side is identically
`1`, the reader's credence tends to `1`, and the uniform-weight bias tends to `−½`
(`halfPair_weightedBias_tendsto`): averaged unbiasedness is not automatic.

**(iii) root-deference-034 ("calibration unsatisfiable on `g_n`")** is reconciled with
`li-diagonal`, not re-proved: true for hard gates (`hard_dichotomy`), false in the limit-point
reading against legal gates (`two_faces_pair`, `theoremC_i`, F-8), open in the full-limit reading
(F-9). Findings F-TwoFaces.

**(iv) v6's own gate on the two-faces witness (repair round 1, audit B4).** v6 §5.10 claims the
bias for the *high-side gate* `Ind_δ(a_n > ½)` whenever `A` does not pin `½`, and for the uniform
weight only in the pinned case. On the alternating table the quotes are `0/1`, so FAF's ramp
`ctsInd δ (a_n) ½` is a positive rescaling of the hard weight `a_n` for every `δ > 0` — equal to
it for `δ ≤ ½` (`ctsInd_aAlt`, `ctsInd_aAlt_eq_smul`) — and, `weightedBias` being invariant under
rescaling the weight (`weightedAverage_smul_weight`), the gated bias tends to **`1`** for every
width (`altPair_highGate_bias_tendsto_one`, `altPair_rampGate_bias_tendsto_one`): on
the package's own witness v6's sentence holds. `altPair_two_faces` is unbiased only under the
uniform weight, which v6 never claims for a non-pinned quote; it is a fact about a different
weighting, not a correction of v6. (On the constant-`½` table the uniform weight's bias `→ −½`
confirms v6's pinned clause.)

Scope: one-way (real sequences over the alternating and constant pairs).
-/

namespace Cleanroom.Deference.DefObstruction

open LogicalInduction LO.Propositional Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Cleanroom.Li.LiDiagonal
open Filter Topology Finset

/-! ## A. The alternating table's bias against its own side -/

/-- The quote-minus-side on the alternating table is `−1` on even days, `+1` on odd days.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem aAlt_sub_side_eq (n : ℕ) :
    (aAlt 0 n : ℝ) - side (aAlt 0) n = if n % 2 = 0 then -1 else 1 := by
  rw [side_aAlt]
  unfold aAlt
  by_cases h : n % 2 = 0 <;> simp [h]

/-- The partial sums of quote-minus-side on the alternating table are `0` or `−1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_aAlt_sub_side (N : ℕ) :
    ∑ i ∈ range N, ((aAlt 0 i : ℝ) - side (aAlt 0) i) = if N % 2 = 0 then 0 else -1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, aAlt_sub_side_eq]
    rcases Nat.mod_two_eq_zero_or_one N with h | h
    · have h' : (N + 1) % 2 = 1 := by omega
      simp [h, h']
    · have h' : (N + 1) % 2 = 0 := by omega
      simp [h, h']

/-- The partial sums are bounded by `1` in absolute value.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem abs_sum_aAlt_sub_side_le (N : ℕ) :
    |∑ i ∈ range N, ((aAlt 0 i : ℝ) - side (aAlt 0) i)| ≤ 1 := by
  rw [sum_aAlt_sub_side]
  split_ifs <;> norm_num

/-- **The Cesàro mean of quote-minus-side on the alternating table tends to `0`** (the mandate's
`cesaro (fun n => aAlt 0 n − s_n) → 0`).
Scope: real sequences.
Source: mandate T5(i)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem cesaro_aAlt_sub_side :
    Tendsto (cesaro (fun n => (aAlt 0 n : ℝ) - side (aAlt 0) n)) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ tendsto_one_div_atTop_nhds_zero_nat
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Real.norm_eq_abs]
  unfold cesaro
  rw [abs_div, abs_of_pos (by exact_mod_cast hN : (0 : ℝ) < N)]
  exact div_le_div_of_nonneg_right (abs_sum_aAlt_sub_side_le N) (Nat.cast_nonneg N)

/-! ## B. T5(i): the realized witness -/

/-- **The uniform-weight bias between the alternating quote and the reader's deferred credence
tends to `0`** (FAF's `weightedBias` at the constant weighting): the quote-minus-side partial
sums are bounded, and the side-minus-credence tends to `0` (Lemma B), so the uniform average of
their sum vanishes.
Scope: one-way (the alternating pair).
Source: mandate T5(i); [[deference-in-logical-induction-v6]] §7 line 812 (the averaged face); root-deference-035; root-fa-038
Kind: N+
Fidelity: exact (FAF's `weightedBias` at `w ≡ 1`; the realized `Y` of FAF's LIA)
Hyps: (a) none -/
theorem altPair_weightedBias_tendsto_zero :
    Tendsto (weightedBias (fun _ => (1 : ℝ)) (fun n => (aAlt 0 n : ℝ)) (altPair.Y succDeferral))
      atTop (𝓝 0) := by
  have h1 : Tendsto (weightedAverage (fun _ => (1 : ℝ))
      (fun i => side (aAlt 0) i - altPair.Y succDeferral i)) atTop (𝓝 0) := by
    apply weightedAverage_tendsto_zero (fun _ => zero_le_one) tendsto_prefixSum_one
    have h := altPair_Y_sub_side
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine h.congr fun n => ?_
    rw [Real.norm_eq_abs, abs_sub_comm]
  have h2 : Tendsto (weightedAverage (fun _ => (1 : ℝ))
      (fun i => (aAlt 0 i : ℝ) - side (aAlt 0) i)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [weightedAverage_one, Real.norm_eq_abs, abs_div,
      abs_of_pos (show (0 : ℝ) < (n : ℝ) + 1 by positivity)]
    exact div_le_div_of_nonneg_right (abs_sum_aAlt_sub_side_le (n + 1))
      (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
  have h3 := h1.add h2
  rw [zero_add] at h3
  unfold weightedBias
  refine h3.congr fun n => ?_
  rw [weightedAverage_one, weightedAverage_one, weightedAverage_one, ← add_div, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro i _
  ring

/-- **The two faces, realized on one coupled instance (T5(i))**: on the alternating pair the
pointwise credence defect tends to `1` while the uniform-weight bias tends to `0`. "Averaged" is
strictly weaker than "pointwise", on a real inductor over a real ledger — not on decoupled
sequences.
Scope: one-way (the alternating pair).
Source: mandate T5(i) (the plan's "pointwise-wrong-yet-aggregate-unbiased witness"); root-deference-035; lean-deference-028 (the decoupled predecessor); root-fa-038
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem altPair_two_faces :
    Tendsto (fun n => |(aAlt 0 n : ℝ) - altPair.Y succDeferral n|) atTop (𝓝 1) ∧
    Tendsto (weightedBias (fun _ => (1 : ℝ)) (fun n => (aAlt 0 n : ℝ)) (altPair.Y succDeferral))
      atTop (𝓝 0) :=
  ⟨altPair_defect_tendsto_one, altPair_weightedBias_tendsto_zero⟩

/-! ## C. T5(ii): both faces can die -/

/-- **On the constant best response the uniform-weight bias tends to `−½`**: the quote is `½`, the
reader's credence tends to `1`, so the averaged face fails there too. Averaged unbiasedness is a
property of *some* quotes, not of all.
Scope: one-way (the constant pair).
Source: mandate T5(ii); [[deference-in-logical-induction-v6]] §4.8/§5.10 ("if `A` pins `½`, the uniform weight carries a persistent bias")
Kind: N+ (a FAF inductor on which the averaged face is refuted)
Fidelity: exact
Hyps: (a) none -/
theorem halfPair_weightedBias_tendsto :
    Tendsto (weightedBias (fun _ => (1 : ℝ)) (fun n => (aHalf 0 n : ℝ)) (halfPair.Y succDeferral))
      atTop (𝓝 (-(1 / 2))) := by
  unfold weightedBias
  apply weightedAverage_tendsto (fun _ => zero_le_one) tendsto_prefixSum_one
  have h := (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub halfPair_Y_tendsto_one
  have e : (1 / 2 : ℝ) - 1 = -(1 / 2) := by norm_num
  rw [e] at h
  refine h.congr fun n => ?_
  norm_num [aHalf]

/-! ## D. v6's high-side gate on the alternating pair: biased by `1` -/

/-- **The high-side gate on the alternating table** `𝟙[aAlt 0 i > ½] = aAlt 0 i` (the quotes are
`0/1`).
Source: [[deference-in-logical-induction-v6]] §5.10 l. 703 ("the high-side gate `Ind_δ(a_n > ½)`"); audit r1 probe `GatedBiasAlt`
Kind: D
Fidelity: exact (on `0/1` quotes the hard gate and the ramp coincide: `ctsInd_aAlt`)
Hyps: n/a -/
noncomputable def wHigh (i : ℕ) : ℝ := (aAlt 0 i : ℝ)

/-- The gate is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem wHigh_nonneg (i : ℕ) : 0 ≤ wHigh i := by
  unfold wHigh; exact_mod_cast (aAlt_range 0 i).1

/-- The gate is idempotent (`0/1`-valued).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem wHigh_sq (i : ℕ) : wHigh i * wHigh i = wHigh i := by
  unfold wHigh aAlt; split_ifs <;> norm_num

/-- The gate kills the side: on gated days the quote is `1`, so the side is `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem wHigh_mul_side (i : ℕ) : wHigh i * side (aAlt 0) i = 0 := by
  unfold wHigh; rw [side_aAlt]; unfold aAlt; split_ifs <;> norm_num

/-- `∑_{i<N} aAlt 0 i = ⌊N/2⌋`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_aAlt (N : ℕ) : ∑ i ∈ range N, (aAlt 0 i : ℝ) = ((N / 2 : ℕ) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    unfold aAlt
    rcases Nat.mod_two_eq_zero_or_one N with h | h
    · have h' : (N + 1) / 2 = N / 2 := by omega
      simp [h, h']
    · have h' : (N + 1) / 2 = N / 2 + 1 := by omega
      simp [h, h']

/-- The gate's prefix sums are `⌊(n+1)/2⌋`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem prefixSum_wHigh (n : ℕ) : prefixSum wHigh n = (((n + 1) / 2 : ℕ) : ℝ) := by
  unfold prefixSum wHigh; exact sum_aAlt (n + 1)

/-- The gate's prefix sums diverge (the gate is legal in FAF's sense: unbounded mass).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tendsto_prefixSum_wHigh : Tendsto (prefixSum wHigh) atTop atTop := by
  have h : Tendsto (fun n : ℕ => (n + 1) / 2) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨2 * b, fun n hn => by omega⟩
  have := (tendsto_natCast_atTop_atTop (R := ℝ)).comp h
  exact this.congr fun n => (prefixSum_wHigh n).symm

/-- **The high-side-gated bias on the alternating pair tends to `1`** — v6's gate, v6's claim, on
the package's two-faces witness: `w_i (a_i − Y_i) = w_i − w_i (Y_i − s_i)` since `w_i² = w_i` and
`w_i s_i = 0`, so the gated average is `1 − wavg_w(Y − s) → 1` by Lemma B. Whatever the uniform
weight does (`altPair_weightedBias_tendsto_zero`), on the gate v6 names the averaged face dies
here, as v6 says.
Scope: one-way (the alternating pair).
Source: [[deference-in-logical-induction-v6]] §4.8 l. 544, §5.10 l. 703–704 ("whatever `A` quotes, the high-side gate … carries a persistent `≥ ½` bias"); audit r1 probe `GatedBiasAlt`
Kind: N+
Fidelity: exact (FAF's `weightedBias` at the hard high-side gate; equal to the ramp for `δ ≤ ½`, `altPair_rampGate_bias_tendsto_one`)
Hyps: (a) none -/
theorem altPair_highGate_bias_tendsto_one :
    Tendsto (weightedBias wHigh (fun n => (aAlt 0 n : ℝ)) (altPair.Y succDeferral))
      atTop (𝓝 1) := by
  have hz : Tendsto (fun i => altPair.Y succDeferral i - side (aAlt 0) i) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using altPair_Y_sub_side
  have h0 : Tendsto (weightedAverage wHigh
      (fun i => altPair.Y succDeferral i - side (aAlt 0) i)) atTop (𝓝 0) :=
    weightedAverage_tendsto_zero wHigh_nonneg tendsto_prefixSum_wHigh hz
  have hev : (fun n => 1 - weightedAverage wHigh
        (fun i => altPair.Y succDeferral i - side (aAlt 0) i) n) =ᶠ[atTop]
      weightedBias wHigh (fun n => (aAlt 0 n : ℝ)) (altPair.Y succDeferral) := by
    filter_upwards [eventually_prefixSum_pos tendsto_prefixSum_wHigh] with n hn
    have hne : prefixSum wHigh n ≠ 0 := hn.ne'
    have ha : weightedAverage wHigh (fun i => (aAlt 0 i : ℝ)) n = 1 := by
      rw [weightedAverage_eq_div hne]
      have hnum : prefixSum (fun i => wHigh i * (aAlt 0 i : ℝ)) n = prefixSum wHigh n := by
        unfold prefixSum; exact sum_congr rfl fun i _ => wHigh_sq i
      rw [hnum, div_self hne]
    have hs : weightedAverage wHigh (fun i => side (aAlt 0) i) n = 0 := by
      rw [weightedAverage_eq_div hne]
      have hnum : prefixSum (fun i => wHigh i * side (aAlt 0) i) n = 0 := by
        unfold prefixSum; exact sum_eq_zero fun i _ => wHigh_mul_side i
      rw [hnum, zero_div]
    unfold weightedBias
    rw [weightedAverage_sub wHigh (altPair.Y succDeferral) (fun i => side (aAlt 0) i) hne,
      weightedAverage_sub wHigh (fun i => (aAlt 0 i : ℝ)) (altPair.Y succDeferral) hne, ha, hs]
    ring
  have h1 := (tendsto_const_nhds (x := (1 : ℝ))).sub h0
  rw [sub_zero] at h1
  exact h1.congr' hev

/-- **On `0/1` quotes v6's ramp is the hard gate**: for `0 < δ ≤ ½`, FAF's `ctsInd δ (aAlt 0 n) ½ =
aAlt 0 n`.
Source: [[deference-in-logical-induction-v6]] §5.10 (`Ind_δ(a_n > ½)`); li-asymp-calc D1 (`ctsInd` is the corpus's ramp)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ctsInd_aAlt {δ : ℚ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (n : ℕ) :
    ctsInd δ (aAlt 0 n : ℝ) (1 / 2) = (aAlt 0 n : ℝ) := by
  have hδ'' : (δ : ℝ) ≤ 1 / 2 := by
    have h : ((δ : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hδ'
    simpa using h
  unfold aAlt
  split_ifs with h
  · simp only [Rat.cast_zero]
    exact (ctsInd_eq_zero_iff hδ _ _).2 (by norm_num)
  · simp only [Rat.cast_one]
    exact (ctsInd_eq_one_iff hδ _ _).2 (by linarith)

/-- **On `0/1` quotes v6's ramp is a positive rescaling of the hard gate, for every width**:
`ctsInd δ (aAlt 0 n) ½ = min 1 (1/(2δ)) · aAlt 0 n` for all `δ > 0` (the factor is `1` for
`δ ≤ ½`, `ctsInd_aAlt`).
Source: [[deference-in-logical-induction-v6]] §5.10; audit r2 N4
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ctsInd_aAlt_eq_smul {δ : ℚ} (hδ : 0 < δ) (n : ℕ) :
    ctsInd δ (aAlt 0 n : ℝ) (1 / 2) = min 1 (1 / (2 * (δ : ℝ))) * (aAlt 0 n : ℝ) := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold aAlt
  split_ifs with h
  · simp only [Rat.cast_zero, mul_zero]
    exact (ctsInd_eq_zero_iff hδ _ _).2 (by norm_num)
  · simp only [Rat.cast_one, mul_one]
    unfold ctsInd
    have h1 : ((1 : ℝ) - 1 / 2) / (δ : ℝ) = 1 / (2 * (δ : ℝ)) := by
      rw [div_eq_div_iff hδR.ne' (by positivity)]
      ring
    have h2 : (0 : ℝ) ≤ 1 / (2 * (δ : ℝ)) := by positivity
    rw [h1, max_eq_right h2]

/-- **A positive rescaling of the weight leaves FAF's `weightedAverage` unchanged**, in both
branches (`prefixSum (c·w) = c · prefixSum w`). FAF API request: scale invariance in the weight.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem weightedAverage_smul_weight (w x : ℕ → ℝ) {c : ℝ} (hc : c ≠ 0) (n : ℕ) :
    weightedAverage (fun i => c * w i) x n = weightedAverage w x n := by
  have hps : prefixSum (fun i => c * w i) n = c * prefixSum w n := by
    simp only [prefixSum, Finset.mul_sum]
  have hpsx : prefixSum (fun i => c * w i * x i) n = c * prefixSum (fun i => w i * x i) n := by
    simp only [prefixSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [weightedAverage]
  rw [hps, hpsx]
  by_cases hden : prefixSum w n = 0
  · simp [hden]
  · rw [if_neg (mul_ne_zero hc hden), if_neg hden, mul_div_mul_left _ _ hc]

/-- **v6's ramp gate `Ind_δ(a_n > ½)` on the alternating pair is biased by `1`, for every width
`δ > 0`**: on `0/1` quotes the ramp is a positive rescaling of the hard gate
(`ctsInd_aAlt_eq_smul`), and FAF's `weightedBias` is invariant under rescaling the weight
(`weightedAverage_smul_weight`). (Repair round 2, audit N4: the round-1 form was restricted to
`0 < δ ≤ ½`, where the ramp *equals* the gate — the restriction bought the identity, not the
conclusion.)
Scope: one-way (the alternating pair).
Source: [[deference-in-logical-induction-v6]] §4.8 l. 544 ("some legal gate"), §5.10 l. 703–704; audit r1 probe `GatedBiasAlt`
Kind: N+
Fidelity: exact (FAF's `weightedBias` at FAF's `ctsInd`, every width)
Hyps: (a) none -/
theorem altPair_rampGate_bias_tendsto_one {δ : ℚ} (hδ : 0 < δ) :
    Tendsto (weightedBias (fun n => ctsInd δ (aAlt 0 n : ℝ) (1 / 2))
      (fun n => (aAlt 0 n : ℝ)) (altPair.Y succDeferral)) atTop (𝓝 1) := by
  have hc : min (1 : ℝ) (1 / (2 * (δ : ℝ))) ≠ 0 := by
    have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
    exact (lt_min one_pos (by positivity)).ne'
  have h : (fun n => ctsInd δ (aAlt 0 n : ℝ) (1 / 2)) =
      fun n => min (1 : ℝ) (1 / (2 * (δ : ℝ))) * wHigh n := by
    funext n; rw [ctsInd_aAlt_eq_smul hδ n]; rfl
  rw [h]
  refine altPair_highGate_bias_tendsto_one.congr fun n => ?_
  unfold weightedBias
  exact (weightedAverage_smul_weight wHigh _ hc n).symm

end Cleanroom.Deference.DefObstruction
