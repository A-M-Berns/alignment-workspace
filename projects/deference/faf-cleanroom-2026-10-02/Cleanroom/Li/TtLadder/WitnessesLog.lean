import Cleanroom.Li.TtLadder.Witnesses
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# `tt-ladder`: witnesses III — the logarithmic witnesses (W1, W3, W7)

Target 5 of [[tt-ladder-mandate]], the FA chat's own witnesses with logarithmic decay, indexed
through `n ↦ n + 2` so that `log (n+2) ≥ log 2 ≥ 1/2 > 0` on every day (the chat's "from
`n ≥ 2`"). There is no `∑ 1/log n = ∞` lemma in this Mathlib; every divergence below is a
comparison with the harmonic series through `log (n+2) ≤ n + 1` (`Real.log_le_sub_one_of_pos`).

* **W1**: `a n = 1/2 + (1/10)/log (n+2)` (gate `min 1 (1/log (n+2))`), `e ≡ 1/10 = t − 2ε₀`:
  `L_prod` holds, `T(1/2, 1/5, 1/10)` fails — the chat's witness for `L_prod ⇏ T(t,ε)`.
* **W3**: `a ≡ 3/5`, `e n = max 0 (1/2 − 1/log (n+2))`: `L_cond`, `T_∀ε`, `¬BV`, `¬T_full`.
* **W7**: `a n = 1/2 + (3/10)/√log (n+2)`, `e n = 1/2 − (3/10)/√log (n+2)`: `Dominates e a`,
  hence `T_full` at every width, while `BV(1/2, 1/10)` fails — "the true residue above the
  theorem is rates and summability". Both sequences non-constant.

Over real sequences; nothing here is a theorem about inductors.
-/

namespace Cleanroom.Li.TtLadder

open LogicalInduction Filter Topology
open Cleanroom.Found.LiAsympCalc

/-! ## `log (n+2)` facts -/

/-- `0 < log (n+2)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem log_add_two_pos (n : ℕ) : 0 < Real.log ((n : ℝ) + 2) :=
  Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])

/-- `1/2 ≤ log (n+2)` (from `1 − 2⁻¹ ≤ log 2`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem log_add_two_ge_half (n : ℕ) : 1/2 ≤ Real.log ((n : ℝ) + 2) := by
  have h2 : (1 : ℝ) - 2⁻¹ ≤ Real.log 2 := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have h3 : Real.log 2 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  norm_num at h2
  linarith

/-- `log (n+2) ≤ n + 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem log_add_two_le (n : ℕ) : Real.log ((n : ℝ) + 2) ≤ (n : ℝ) + 1 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n : ℝ) + 2 by
    linarith [Nat.cast_nonneg (α := ℝ) n])
  linarith

/-- `log (n+2) → ∞`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem tendsto_log_add_two : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

/-- `1/log (n+2) → 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem tendsto_one_div_log_add_two :
    Tendsto (fun n : ℕ => 1 / Real.log ((n : ℝ) + 2)) atTop (𝓝 0) := by
  have := tendsto_log_add_two.inv_tendsto_atTop
  refine this.congr (fun n => ?_)
  simp [one_div]

/-- `1/(n+1) ≤ 1/log (n+2)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem one_div_succ_le_one_div_log (n : ℕ) :
    1 / ((n : ℝ) + 1) ≤ 1 / Real.log ((n : ℝ) + 2) :=
  one_div_le_one_div_of_le (log_add_two_pos n) (log_add_two_le n)

/-! ## W1 -/

/-- W1's quote `1/2 + (1/10)/log (n+2)`.
Source: lean-deference-2-003 (W1); lean-deference-046 (W1)
Kind: D
Fidelity: variant: reindexed by `n + 2`
Hyps: n/a -/
noncomputable def w1Quote (n : ℕ) : ℝ := 1/2 + (1/10) / Real.log ((n : ℝ) + 2)

/-- `w1Quote n ∈ [1/2, 7/10]`.
Source: lean-deference-2-003 (W1)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem w1Quote_bounds (n : ℕ) : 1/2 ≤ w1Quote n ∧ w1Quote n ≤ 7/10 := by
  have h1 : (1/10 : ℝ) / Real.log ((n : ℝ) + 2) ≤ (1/10) / (1/2) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (log_add_two_ge_half n)
  have h0 : 0 ≤ (1/10 : ℝ) / Real.log ((n : ℝ) + 2) := div_nonneg (by norm_num) (log_add_two_pos n).le
  unfold w1Quote
  constructor <;> linarith

/-- W1's gate at `(1/2, 1/10)` is `min 1 (1/log (n+2))`.
Source: lean-deference-2-003 (W1: `G_n = min(1/ln n, 1)`)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem gateSeq_w1Quote (n : ℕ) :
    gateSeq (1/2) (1/10) w1Quote n = min 1 (1 / Real.log ((n : ℝ) + 2)) := by
  have hL := log_add_two_pos n
  have h0 : 0 ≤ (1/10 : ℝ) / Real.log ((n : ℝ) + 2) := div_nonneg (by norm_num) hL.le
  unfold gateSeq w1Quote
  rw [ctsInd_of_le (by norm_num) (by push_cast; linarith)]
  congr 1
  push_cast
  field_simp
  ring

/-- W1's gate is `≥ 1/(n+1)` and tends to `0`.
Source: lean-deference-2-003 (W1)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem gateSeq_w1Quote_ge (n : ℕ) : 1 / ((n : ℝ) + 1) ≤ gateSeq (1/2) (1/10) w1Quote n := by
  rw [gateSeq_w1Quote]
  refine le_min ?_ (one_div_succ_le_one_div_log n)
  rw [div_le_one (by positivity)]
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- W1's gate tends to `0`.
Source: lean-deference-2-003 (W1)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem tendsto_gateSeq_w1Quote : Tendsto (gateSeq (1/2) (1/10) w1Quote) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_one_div_log_add_two
    (fun n => gateSeq_nonneg _ _ _ n) (fun n => by rw [gateSeq_w1Quote]; exact min_le_right _ _)

/-- **W1, `L_prod`**: `G_n (1/10 − 1/2) = −(2/5) G_n → 0`.
Source: lean-deference-2-003 (W1); lean-deference-046
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem lProdSeq_w1 : LProdSeq w1Quote (fun _ => 1/10) (1/2) (1/10) := by
  intro η hη
  filter_upwards [tendsto_gateSeq_w1Quote.eventually (gt_mem_nhds hη)] with n hn
  show (0 : ℝ) ≤ gateSeq (1/2) (1/10) w1Quote n * (1/10 - ((1/2 : ℚ) : ℝ)) + η
  have := gateSeq_nonneg (1/2) (1/10) w1Quote n
  push_cast
  linarith

/-- **W1, `¬T(1/2, 1/5, 1/10)`**: the violation ramp at `e ≡ 1/10 = t − 2ε₀` saturates, so the
weight is the gate, which is `≥ 1/(n+1)`.
Source: lean-deference-2-003 (W1: `∑ 1/ln n = ∞`); lean-deference-046
Kind: P
Fidelity: exact (divergence by harmonic comparison, not by a `1/log` lemma)
Hyps: (a) none -/
theorem not_tSeq_w1 : ¬ TSeq w1Quote (fun _ => 1/10) (1/2) (1/5) (1/10) := by
  unfold TSeq
  refine not_summable_of_one_div_succ_le one_pos (fun n => ?_)
  rw [viol_eq_gateSeq_mul, (ctsInd_eq_one_iff (by norm_num) _ _).2 (by norm_num), mul_one]
  exact gateSeq_w1Quote_ge n

/-- **W1** (`N+`, non-constant quote): the chat's own witness for `L_prod ⇏ T(t,ε)`.
Source: lean-deference-2-003 (W1); lean-deference-046
Kind: N+
Fidelity: variant: reindexed by `n + 2`
Hyps: n/a -/
theorem w1_witness :
    (∀ n, w1Quote n ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ n, (fun _ : ℕ => (1/10 : ℝ)) n ∈ Set.Icc (0 : ℝ) 1) ∧
    LProdSeq w1Quote (fun _ => 1/10) (1/2) (1/10) ∧
    ¬ TSeq w1Quote (fun _ => 1/10) (1/2) (1/5) (1/10) :=
  ⟨fun n => ⟨by linarith [(w1Quote_bounds n).1], by linarith [(w1Quote_bounds n).2]⟩,
    fun _ => ⟨by norm_num, by norm_num⟩, lProdSeq_w1, not_tSeq_w1⟩

/-- **Non-arrow `L_prod ⇏ T(t,ε,δ)`** at `t = 1/2, ε = 1/5, δ = 1/10` by W1 (the chat's witness;
`lProdSeq_not_tSeq` in `Witnesses.lean` is W4's).
Source: lean-deference-2-002 ("`L_prod ⇏ T(t,ε)` (W1)"); [[faithful-acceleration]] l.128–130
Kind: N+
Fidelity: variant: sequence-level
Hyps: n/a -/
theorem lProdSeq_not_tSeq_w1 :
    ∃ a e : ℕ → ℝ, (∀ n, a n ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ n, e n ∈ Set.Icc (0 : ℝ) 1) ∧
      LProdSeq a e (1/2) (1/10) ∧ ¬ TSeq a e (1/2) (1/5) (1/10) :=
  ⟨_, _, w1_witness.1, w1_witness.2.1, w1_witness.2.2.1, w1_witness.2.2.2⟩

/-! ## W3 -/

/-- W3's credence `max 0 (1/2 − 1/log (n+2))`.
Source: lean-deference-2-003 (W3)
Kind: D
Fidelity: variant: reindexed by `n + 2`
Hyps: n/a -/
noncomputable def w3E (n : ℕ) : ℝ := max 0 (1/2 - 1 / Real.log ((n : ℝ) + 2))

/-- `w3E n ∈ [0, 1/2]`.
Source: lean-deference-2-003 (W3)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem w3E_bounds (n : ℕ) : 0 ≤ w3E n ∧ w3E n ≤ 1/2 := by
  have h0 : 0 ≤ 1 / Real.log ((n : ℝ) + 2) := div_nonneg zero_le_one (log_add_two_pos n).le
  unfold w3E
  exact ⟨le_max_left _ _, max_le (by norm_num) (by linarith)⟩

/-- **W3, `L_cond`**: `1/log (n+2) → 0`, so `e n ≥ 1/2 − 1/log (n+2)` is eventually above
`1/2 − c`.
Source: lean-deference-2-003 (W3: "`L_cond(t)` holds")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem lCondSeq_w3 : LCondSeq (fun _ => 3/5) w3E (1/2) := by
  intro c hc
  filter_upwards [tendsto_one_div_log_add_two.eventually (gt_mem_nhds hc)] with n hn _
  unfold w3E
  push_cast
  have := le_max_right (0 : ℝ) (1/2 - 1 / Real.log ((n : ℝ) + 2))
  linarith

/-- **W3, `¬BV`**: the margin-free ramp is `≥ min 1 (10 · min (1/2) (1/log (n+2))) ≥ 1/(n+1)`.
Source: lean-deference-2-003 (W3: "`∑ Ind_δ(E^H < t) ≈ ∑ 1/(δ ln n) = ∞`")
Kind: P
Fidelity: exact (harmonic comparison)
Hyps: (a) none -/
theorem not_bvSeq_w3 : ¬ BVSeq (fun _ => 3/5) w3E (1/2) (1/10) := by
  unfold BVSeq
  refine not_summable_of_one_div_succ_le one_pos (fun n => ?_)
  rw [gateSeq_const_three_fifths, one_mul]
  have hL := log_add_two_pos n
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hgap : min (1/2 : ℝ) (1 / Real.log ((n : ℝ) + 2)) ≤ ((1/2 : ℚ) : ℝ) - w3E n := by
    unfold w3E
    push_cast
    rcases le_or_gt (1/2 - 1 / Real.log ((n : ℝ) + 2)) 0 with h | h
    · rw [max_eq_left h]; linarith [min_le_left (1/2 : ℝ) (1 / Real.log ((n : ℝ) + 2))]
    · rw [max_eq_right h.le]
      linarith [min_le_right (1/2 : ℝ) (1 / Real.log ((n : ℝ) + 2))]
  refine le_trans ?_ (min_one_div_le_ctsInd (by norm_num) hgap)
  refine le_min ?_ ?_
  · rw [div_le_one hn1]; linarith [Nat.cast_nonneg (α := ℝ) n]
  · push_cast
    rw [le_div_iff₀ (by norm_num)]
    refine le_min ?_ ?_
    · rw [div_mul_eq_mul_div, div_le_iff₀ hn1]; linarith [Nat.cast_nonneg (α := ℝ) n]
    · have := one_div_succ_le_one_div_log n
      have h0 : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
      linarith

/-- **W3, `¬T_full`**: `e ≤ 1/2 < 11/20 = a − 1/20`, so `e` never dominates `a`.
Source: lean-deference-2-003 (W3: `liminf(E^H − a) = −δ`)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem not_tFullSeq_w3 : ¬ TFullSeq (fun _ => 3/5) w3E (1/10) := by
  intro h
  have hdom := dominates_of_tFullSeq (fun _ => ⟨by norm_num, by norm_num⟩) (by norm_num) h
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hdom (1/20) (by norm_num))
  have := hN N le_rfl
  have := (w3E_bounds N).2
  linarith

/-- **W3** (`N+`, non-constant credence): `a ≡ 3/5`, `e n = max 0 (1/2 − 1/log (n+2))`:
`L_cond`, `L_prod`, `T_∀ε` at `t = 1/2, δ = 1/10`; `BV` fails; `T_full(1/10)` fails. Same
verdicts as creep (`creep_witness`), with the chat's logarithmic profile.
Source: lean-deference-2-003 (W3)
Kind: N+
Fidelity: variant: reindexed by `n + 2`
Hyps: n/a -/
theorem w3_witness :
    (∀ n, (fun _ : ℕ => (3/5 : ℝ)) n ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ n, w3E n ∈ Set.Icc (0 : ℝ) 1) ∧
    LCondSeq (fun _ => 3/5) w3E (1/2) ∧
    LProdSeq (fun _ => 3/5) w3E (1/2) (1/10) ∧
    TAllEpsSeq (fun _ => 3/5) w3E (1/2) (1/10) ∧
    ¬ BVSeq (fun _ => 3/5) w3E (1/2) (1/10) ∧
    ¬ TFullSeq (fun _ => 3/5) w3E (1/10) :=
  ⟨fun _ => ⟨by norm_num, by norm_num⟩,
    fun n => ⟨(w3E_bounds n).1, by linarith [(w3E_bounds n).2]⟩,
    lCondSeq_w3, lProdSeq_of_lCondSeq (by norm_num) lCondSeq_w3,
    tAllEpsSeq_of_lCondSeq (by norm_num) lCondSeq_w3, not_bvSeq_w3, not_tFullSeq_w3⟩

/-! ## W7 -/

/-- The common decay `(3/10)/√log (n+2)` of W7.
Source: lean-deference-2-003 (W7)
Kind: D
Fidelity: variant: reindexed by `n + 2`
Hyps: n/a -/
noncomputable def w7Decay (n : ℕ) : ℝ := (3/10) / Real.sqrt (Real.log ((n : ℝ) + 2))

/-- W7's quote `1/2 + (3/10)/√log (n+2)`.
Source: lean-deference-2-003 (W7)
Kind: D
Fidelity: variant: reindexed by `n + 2`
Hyps: n/a -/
noncomputable def w7Quote (n : ℕ) : ℝ := 1/2 + w7Decay n

/-- W7's credence `1/2 − (3/10)/√log (n+2)`.
Source: lean-deference-2-003 (W7)
Kind: D
Fidelity: variant: reindexed by `n + 2`
Hyps: n/a -/
noncomputable def w7E (n : ℕ) : ℝ := 1/2 - w7Decay n

/-- `3/5 ≤ √log (n+2)` (from `log (n+2) ≥ 1/2 ≥ 9/25`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem sqrt_log_add_two_ge (n : ℕ) : 3/5 ≤ Real.sqrt (Real.log ((n : ℝ) + 2)) := by
  rw [Real.le_sqrt (by norm_num) (log_add_two_pos n).le]
  linarith [log_add_two_ge_half n]

/-- `0 < √log (n+2)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem sqrt_log_add_two_pos (n : ℕ) : 0 < Real.sqrt (Real.log ((n : ℝ) + 2)) :=
  Real.sqrt_pos.2 (log_add_two_pos n)

/-- `0 ≤ w7Decay n ≤ 1/2`.
Source: lean-deference-2-003 (W7: bounds)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem w7Decay_bounds (n : ℕ) : 0 ≤ w7Decay n ∧ w7Decay n ≤ 1/2 := by
  unfold w7Decay
  constructor
  · exact div_nonneg (by norm_num) (sqrt_log_add_two_pos n).le
  · rw [div_le_iff₀ (sqrt_log_add_two_pos n)]
    linarith [sqrt_log_add_two_ge n]

/-- `w7Quote n ∈ [1/2, 1]` and `w7E n ∈ [0, 1/2]`.
Source: lean-deference-2-003 (W7)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem w7_bounds (n : ℕ) :
    w7Quote n ∈ Set.Icc (0 : ℝ) 1 ∧ w7E n ∈ Set.Icc (0 : ℝ) 1 := by
  have := w7Decay_bounds n
  unfold w7Quote w7E
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- **W7, `Dominates`**: `a − e = (3/5)/√log (n+2) → 0`, so `e` dominates `a` at every margin.
Source: lean-deference-2-003 (W7: `liminf(E^H − a) = 0`)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem dominates_w7 : Dominates w7E w7Quote := by
  intro c hc
  have hK : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2)) atTop atTop := tendsto_log_add_two
  filter_upwards [hK.eventually (eventually_gt_atTop (((3/5) / c) ^ 2))] with n hn
  have hs : (3/5) / c < Real.sqrt (Real.log ((n : ℝ) + 2)) :=
    (Real.lt_sqrt (div_nonneg (by norm_num) hc.le)).2 hn
  have hpos := sqrt_log_add_two_pos n
  rw [div_lt_iff₀ hc] at hs
  unfold w7E w7Quote w7Decay
  have : (3/10 : ℝ) / Real.sqrt (Real.log ((n : ℝ) + 2)) < c / 2 := by
    rw [div_lt_iff₀ hpos]; linarith
  linarith

/-- **W7, `T_full` at every width**: from dominance.
Source: lean-deference-2-003 (W7: "`T_full` holds")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem tFullSeq_w7 {δ : ℚ} (hδ : 0 < δ) : TFullSeq w7Quote w7E δ :=
  tFullSeq_of_dominates hδ dominates_w7

/-- **W7, `¬BV(1/2, 1/10)`**: both ramps are `min 1 (3/√log (n+2))`, each `≥ 1/√(n+1)`, so the
weight is `≥ 1/(n+1)` — harmonic.
Source: lean-deference-2-003 (W7: "`G_n · Ind_δ(E^H < t) ≈ 1/(δ² ln n)` is not summable")
Kind: P
Fidelity: exact (harmonic comparison)
Hyps: (a) none -/
theorem not_bvSeq_w7 : ¬ BVSeq w7Quote w7E (1/2) (1/10) := by
  unfold BVSeq
  refine not_summable_of_one_div_succ_le one_pos (fun n => ?_)
  have hs := sqrt_log_add_two_pos n
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsn : Real.sqrt (Real.log ((n : ℝ) + 2)) ≤ Real.sqrt ((n : ℝ) + 1) :=
    Real.sqrt_le_sqrt (log_add_two_le n)
  have hsn1 : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) := by
    rw [Real.le_sqrt (by norm_num) hn1.le]; linarith
  have hsn1' : 0 < Real.sqrt ((n : ℝ) + 1) := by linarith
  -- the common lower bound on both ramps
  have hs' := hs.ne'
  have hval : w7Decay n / ((1/10 : ℚ) : ℝ) = 3 / Real.sqrt (Real.log ((n : ℝ) + 2)) := by
    unfold w7Decay
    push_cast
    field_simp
    try ring
  have hlow : 1 / Real.sqrt ((n : ℝ) + 1) ≤ min 1 (w7Decay n / ((1/10 : ℚ) : ℝ)) := by
    refine le_min ?_ ?_
    · rw [div_le_one hsn1']; exact hsn1
    · rw [hval]
      calc 1 / Real.sqrt ((n : ℝ) + 1) ≤ 1 / Real.sqrt (Real.log ((n : ℝ) + 2)) :=
            one_div_le_one_div_of_le hs hsn
        _ ≤ 3 / Real.sqrt (Real.log ((n : ℝ) + 2)) := by
            rw [div_le_div_iff_of_pos_right hs]; norm_num
  have hg : min 1 (w7Decay n / ((1/10 : ℚ) : ℝ)) ≤ gateSeq (1/2) (1/10) w7Quote n :=
    min_one_div_le_ctsInd (by norm_num) (by unfold w7Quote; push_cast; linarith)
  have hr : min 1 (w7Decay n / ((1/10 : ℚ) : ℝ)) ≤ ctsInd (1/10) ((1/2 : ℚ) : ℝ) (w7E n) :=
    min_one_div_le_ctsInd (by norm_num) (by unfold w7E; push_cast; linarith)
  have hsq : 1 / Real.sqrt ((n : ℝ) + 1) * (1 / Real.sqrt ((n : ℝ) + 1)) = 1 / ((n : ℝ) + 1) := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hn1.le]
  calc 1 / ((n : ℝ) + 1) = 1 / Real.sqrt ((n : ℝ) + 1) * (1 / Real.sqrt ((n : ℝ) + 1)) := hsq.symm
    _ ≤ gateSeq (1/2) (1/10) w7Quote n * ctsInd (1/10) ((1/2 : ℚ) : ℝ) (w7E n) :=
        mul_le_mul (hlow.trans hg) (hlow.trans hr) (by positivity) (gateSeq_nonneg _ _ _ _)

/-- **W7** (`N+`, both sequences non-constant — the package's load-bearing residue witness):
`a n = 1/2 + (3/10)/√log (n+2)`, `e n = 1/2 − (3/10)/√log (n+2)`: `e` dominates `a`, so
`T_full` holds at every width, yet `BV(1/2, 1/10)` fails — the only thing above the theorem
family is summability/rates.
Source: lean-deference-2-003 (W7); lean-deference-2-004 (iv); lean-deference-046
Kind: N+
Fidelity: variant: reindexed by `n + 2`
Hyps: n/a -/
theorem w7_witness :
    (∀ n, w7Quote n ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ n, w7E n ∈ Set.Icc (0 : ℝ) 1) ∧
    Dominates w7E w7Quote ∧ (∀ δ : ℚ, 0 < δ → TFullSeq w7Quote w7E δ) ∧
    ¬ BVSeq w7Quote w7E (1/2) (1/10) :=
  ⟨fun n => (w7_bounds n).1, fun n => (w7_bounds n).2, dominates_w7, fun _ hδ => tFullSeq_w7 hδ,
    not_bvSeq_w7⟩

/-- **Strictness of `∀ t · BV ⇒ T_full`** (W7): `T_full(1/10)` with `BV(1/2, 1/10)` failing.
Source: lean-deference-2-004 (iv)
Kind: N+
Fidelity: variant: sequence-level
Hyps: n/a -/
theorem tFullSeq_not_bvSeq :
    ∃ a e : ℕ → ℝ, (∀ n, a n ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ n, e n ∈ Set.Icc (0 : ℝ) 1) ∧
      TFullSeq a e (1/10) ∧ ¬ BVSeq a e (1/2) (1/10) :=
  ⟨_, _, w7_witness.1, w7_witness.2.1, w7_witness.2.2.2.1 (1/10) (by norm_num),
    w7_witness.2.2.2.2⟩

end Cleanroom.Li.TtLadder
