import Cleanroom.Li.TtLadder.WitnessesLog
import Cleanroom.Li.TtLadder.WitnessesConst
import Cleanroom.Li.TtLadder.Closure

/-!
# `tt-ladder`: the ladder's rate structure — a quantitative Hasse diagram (extension)

Target 8 of [[tt-ladder-mandate]]: for each strict rung, the slowest-decaying gap that separates
it from the next, over real sequences.

* **`T_full → ∀t·BV` is an `L²` rung**: `∑ ((a − e)⁺)² < ∞` gives `BV(t,δ)` at every threshold
  and width (`bvSeq_of_summable_sq`: on a gate day both ramps are linear, `≤ (a−t)⁺/δ` and
  `≤ (t−e)⁺/δ`, and AM–GM bounds their product by `((a−e)⁺)²/(4δ²)`). Sharp at a straddled
  threshold: for `a n = t + r n/2`, `e n = t − r n/2` with `0 ≤ r n ≤ 2δ`,
  `BV(t,δ) ⟺ ∑ r² < ∞` (`bvSeq_straddle_iff`). The two sides: `r n = (1/5)/√(n+1)` (`T_full`,
  `¬BV`) and `r n = (1/5)/(n+1)` (`∀t·BV`). The straddle is essential: `a ≡ 1`,
  `e n = 1 − 1/√(n+2)` satisfy `∀t·BV` with `∑ (a − e)² = ∞` (`bvSeq_all_not_summable_sq`).
* **`BV(t) ↔ T_∀ε(t)` at fixed `t` under the solid gate is an `L¹` rung**: `e n = t − r n` with
  `0 ≤ r n ≤ δ` on **every** day, `r → 0`: `T_∀ε` always, `BV(t,δ) ⟺ ∑ r < ∞`
  (`bvSeq_solid_iff`). Its two sides at the package's width `(t, δ) = (1/2, 1/10)`, quote
  `a ≡ 3/5`: `r n = 1/(n+10)` (`solid_harmonic_witness`: `T_∀ε ∧ ¬BV`) and `r n = 1/(n+10)²`
  (`solid_sq_witness`: `T_∀ε ∧ BV`). The package's creep (`r = 1/(n+2)`, `r 0 = 1/2 > δ`) is
  *not* an instance of the lemma — only its tail from day `8` satisfies `r ≤ δ` (repair round 2,
  audit r2 adversarial B1).
* **`L_prod → T(t,ε)` with a parked violation `e ≡ t − 2ε`** is exactly "summable versus null
  gate mass": `T(t,ε,δ) ⟺ ∑ G < ∞` and `L_prod(t,δ) ⟺ G → 0` (`tSeq_parked_iff`,
  `lProdSeq_parked_iff`).

Over real sequences; nothing here is a theorem about inductors.
-/

namespace Cleanroom.Li.TtLadder

open LogicalInduction Filter Topology
open Cleanroom.Found.LiAsympCalc

/-! ## The `L²` rung -/

/-- **`L²` sufficiency for `∀t·BV`**: `∑ ((a − e)⁺)² < ∞` gives `BV(t,δ)` for every rational
`t` and width `δ > 0`, termwise `G_n · Ind_δ(e_n < t) ≤ ((a_n − e_n)⁺)²/(4δ²)`.
Source: [[tt-ladder-mandate]] target 8 (the `L²` rung)
Kind: P
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem bvSeq_of_summable_sq {a e : ℕ → ℝ} (h : Summable (fun n => (max 0 (a n - e n)) ^ 2))
    (t : ℚ) {δ : ℚ} (hδ : 0 < δ) : BVSeq a e t δ := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold BVSeq
  refine (h.mul_left (1 / (4 * (δ : ℝ) ^ 2))).of_nonneg_of_le
    (fun n => mul_nonneg (gateSeq_nonneg _ _ _ _) (ctsInd_nonneg _ _ _)) (fun n => ?_)
  unfold gateSeq ctsInd
  rcases le_or_gt (a n) t with h1 | h1
  · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hδR.le),
      min_eq_right zero_le_one, zero_mul]
    positivity
  rcases le_or_gt (t : ℝ) (e n) with h2 | h2
  · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith : (t : ℝ) - e n ≤ 0) hδR.le),
      min_eq_right zero_le_one, mul_zero]
    positivity
  · have hx : 0 < (a n - t) / δ := div_pos (by linarith) hδR
    have hy : 0 < ((t : ℝ) - e n) / δ := div_pos (by linarith) hδR
    rw [max_eq_right hx.le, max_eq_right hy.le,
      max_eq_right (by linarith : (0 : ℝ) ≤ a n - e n)]
    have hsq : 1 / (4 * (δ : ℝ) ^ 2) * (a n - e n) ^ 2 =
        ((a n - t) / δ + ((t : ℝ) - e n) / δ) ^ 2 / 4 := by
      field_simp
      ring
    rw [hsq]
    calc min 1 ((a n - t) / δ) * min 1 (((t : ℝ) - e n) / δ)
        ≤ (a n - t) / δ * (((t : ℝ) - e n) / δ) :=
          mul_le_mul (min_le_right _ _) (min_le_right _ _) (le_min zero_le_one hy.le) hx.le
      _ ≤ ((a n - t) / δ + ((t : ℝ) - e n) / δ) ^ 2 / 4 := by
          nlinarith [sq_nonneg ((a n - t) / δ - ((t : ℝ) - e n) / δ)]

/-- **Sharpness at a straddled threshold**: for `a n = t + r n/2`, `e n = t − r n/2` with
`0 ≤ r n ≤ 2δ` (both ramps in their linear range), `BV(t,δ) ⟺ ∑ (r n)² < ∞` — the weight is
exactly `(r n)²/(4δ²)`.
Source: [[tt-ladder-mandate]] target 8 (sharpness)
Kind: P
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem bvSeq_straddle_iff {r : ℕ → ℝ} {t δ : ℚ} (hδ : 0 < δ) (hr : ∀ n, 0 ≤ r n ∧ r n ≤ 2 * δ) :
    BVSeq (fun n => (t : ℝ) + r n / 2) (fun n => (t : ℝ) - r n / 2) t δ ↔
      Summable (fun n => r n ^ 2) := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hterm : ∀ n, gateSeq t δ (fun n => (t : ℝ) + r n / 2) n * ctsInd δ (t : ℝ) ((t : ℝ) - r n / 2)
      = (1 / (4 * (δ : ℝ) ^ 2)) * r n ^ 2 := by
    intro n
    unfold gateSeq
    rw [ctsInd_of_le hδ (by linarith [(hr n).1]), ctsInd_of_le hδ (by linarith [(hr n).1])]
    have h1 : ((t : ℝ) + r n / 2 - t) / δ = r n / (2 * δ) := by field_simp; ring
    have h2 : ((t : ℝ) - ((t : ℝ) - r n / 2)) / δ = r n / (2 * δ) := by field_simp; ring
    have h3 : r n / (2 * (δ : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact (hr n).2
    rw [h1, h2, min_eq_right h3]
    field_simp
    ring
  unfold BVSeq
  simp only [hterm]
  exact summable_mul_left_iff (by positivity)

/-- The straddle profile `(1/5)/√(n+1)`: `∑ r² = ∑ (1/25)/(n+1) = ∞`, and the pair straddling
`1/2` with it (`a = 1/2 + r/2 ∈ [1/2, 3/5]`, `e = 1/2 − r/2 ∈ [2/5, 1/2]`, both non-constant)
is dominated (its gap tends to `0`), hence satisfies `T_full` at every width, but not
`BV(1/2, 1/10)`. The `[0,1]` bounds and `T_full` are in the statement.
Source: [[tt-ladder-mandate]] target 8 (W7's side of the `L²` rung, with a rational-index profile)
Kind: N+
Fidelity: variant: `1/√(n+1)` in place of W7's `1/√log (n+2)`
Hyps: n/a -/
theorem straddle_sqrt_witness :
    let r : ℕ → ℝ := fun n => (1/5) / Real.sqrt ((n : ℝ) + 1)
    (∀ n, 0 ≤ r n ∧ r n ≤ 2 * ((1/10 : ℚ) : ℝ)) ∧
      (∀ n, ((1/2 : ℚ) : ℝ) + r n / 2 ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ n, ((1/2 : ℚ) : ℝ) - r n / 2 ∈ Set.Icc (0 : ℝ) 1) ∧
      ¬ Summable (fun n => r n ^ 2) ∧
      Dominates (fun n => ((1/2 : ℚ) : ℝ) - r n / 2) (fun n => ((1/2 : ℚ) : ℝ) + r n / 2) ∧
      (∀ δ : ℚ, 0 < δ →
        TFullSeq (fun n => ((1/2 : ℚ) : ℝ) + r n / 2) (fun n => ((1/2 : ℚ) : ℝ) - r n / 2) δ) ∧
      ¬ BVSeq (fun n => ((1/2 : ℚ) : ℝ) + r n / 2) (fun n => ((1/2 : ℚ) : ℝ) - r n / 2)
        (1/2) (1/10) := by
  intro r
  have hsq : ∀ n : ℕ, (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) := fun n => Real.sqrt_pos.2 (by positivity)
  have hs1 : ∀ n : ℕ, (1 : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) := fun n => by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hr : ∀ n, 0 ≤ r n ∧ r n ≤ 2 * ((1/10 : ℚ) : ℝ) := fun n => by
    refine ⟨div_nonneg (by norm_num) (hsq n).le, ?_⟩
    show (1/5 : ℝ) / Real.sqrt ((n : ℝ) + 1) ≤ 2 * ((1/10 : ℚ) : ℝ)
    push_cast
    rw [div_le_iff₀ (hsq n)]
    linarith [hs1 n]
  have hr2 : ∀ n : ℕ, r n ^ 2 = (1/25) / ((n : ℝ) + 1) := fun n => by
    show ((1/5 : ℝ) / Real.sqrt ((n : ℝ) + 1)) ^ 2 = (1/25) / ((n : ℝ) + 1)
    rw [div_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have hlim : Tendsto r atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 1)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have := (h1.inv_tendsto_atTop).const_mul (1/5 : ℝ)
    rw [mul_zero] at this
    refine this.congr (fun n => ?_)
    show (1/5 : ℝ) * (Real.sqrt ((n : ℝ) + 1))⁻¹ = (1/5) / Real.sqrt ((n : ℝ) + 1)
    exact (div_eq_mul_inv _ _).symm
  have hdom : Dominates (fun n => ((1/2 : ℚ) : ℝ) - r n / 2)
      (fun n => ((1/2 : ℚ) : ℝ) + r n / 2) := by
    intro c hc
    filter_upwards [hlim.eventually (gt_mem_nhds hc)] with n hn
    linarith [(hr n).1]
  have hbounds : ∀ n, ((1/2 : ℚ) : ℝ) + r n / 2 ∈ Set.Icc (0 : ℝ) 1 ∧
      ((1/2 : ℚ) : ℝ) - r n / 2 ∈ Set.Icc (0 : ℝ) 1 := fun n => by
    have := hr n
    simp only [Set.mem_Icc]
    push_cast at this ⊢
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith [this.1, this.2]
  refine ⟨hr, fun n => (hbounds n).1, fun n => (hbounds n).2, ?_, hdom,
    fun δ hδ => tFullSeq_of_dominates hδ hdom, ?_⟩
  · intro h
    refine not_summable_of_one_div_succ_le (c := 1/25) (by norm_num) (fun n => ?_) h
    rw [hr2]
  · rw [bvSeq_straddle_iff (by norm_num) hr]
    intro h
    exact not_summable_of_one_div_succ_le (c := 1/25) (by norm_num) (fun n => by rw [hr2]) h

/-- The straddle profile `(1/5)/(n+1)`: `∑ r² < ∞`, so the pair straddling `1/2` with it
(`a = 1/2 + r/2`, `e = 1/2 − r/2`, both in `[0,1]` and non-constant) is dominated, satisfies
`T_full` at every width, and satisfies `BV` at **every** threshold and width (through the `L²`
lemma). The `[0,1]` bounds, `Dominates` and `T_full` are in the statement.
Source: [[tt-ladder-mandate]] target 8 (the summable side of the `L²` rung)
Kind: N+
Fidelity: variant: sequence-level
Hyps: n/a -/
theorem straddle_harmonic_witness :
    let r : ℕ → ℝ := fun n => (1/5) / ((n : ℝ) + 1)
    (∀ n, 0 ≤ r n ∧ r n ≤ 2 * ((1/10 : ℚ) : ℝ)) ∧
      (∀ n, ((1/2 : ℚ) : ℝ) + r n / 2 ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ n, ((1/2 : ℚ) : ℝ) - r n / 2 ∈ Set.Icc (0 : ℝ) 1) ∧
      Summable (fun n => r n ^ 2) ∧
      Dominates (fun n => ((1/2 : ℚ) : ℝ) - r n / 2) (fun n => ((1/2 : ℚ) : ℝ) + r n / 2) ∧
      (∀ δ : ℚ, 0 < δ →
        TFullSeq (fun n => ((1/2 : ℚ) : ℝ) + r n / 2) (fun n => ((1/2 : ℚ) : ℝ) - r n / 2) δ) ∧
      (∀ (t : ℚ) {δ : ℚ}, 0 < δ →
        BVSeq (fun n => ((1/2 : ℚ) : ℝ) + r n / 2) (fun n => ((1/2 : ℚ) : ℝ) - r n / 2) t δ) := by
  intro r
  have hr : ∀ n, 0 ≤ r n ∧ r n ≤ 2 * ((1/10 : ℚ) : ℝ) := fun n => by
    refine ⟨by positivity, ?_⟩
    show (1/5 : ℝ) / ((n : ℝ) + 1) ≤ 2 * ((1/10 : ℚ) : ℝ)
    push_cast
    rw [div_le_iff₀ (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hr2 : ∀ n : ℕ, r n ^ 2 = (1/25) * (1 / ((n : ℝ) + 1) ^ 2) := fun n => by
    show ((1/5 : ℝ) / ((n : ℝ) + 1)) ^ 2 = (1/25) * (1 / ((n : ℝ) + 1) ^ 2)
    rw [div_pow]
    ring
  have hsum : Summable (fun n => r n ^ 2) := by
    simp only [hr2]
    exact summable_one_div_succ_sq.mul_left _
  have hlim : Tendsto r atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1/5 : ℝ)
    rw [mul_zero] at this
    refine this.congr (fun n => ?_)
    show (1/5 : ℝ) * (1 / ((n : ℝ) + 1)) = (1/5) / ((n : ℝ) + 1)
    ring
  have hdom : Dominates (fun n => ((1/2 : ℚ) : ℝ) - r n / 2)
      (fun n => ((1/2 : ℚ) : ℝ) + r n / 2) := by
    intro c hc
    filter_upwards [hlim.eventually (gt_mem_nhds hc)] with n hn
    linarith [(hr n).1]
  have hbounds : ∀ n, ((1/2 : ℚ) : ℝ) + r n / 2 ∈ Set.Icc (0 : ℝ) 1 ∧
      ((1/2 : ℚ) : ℝ) - r n / 2 ∈ Set.Icc (0 : ℝ) 1 := fun n => by
    have := hr n
    simp only [Set.mem_Icc]
    push_cast at this ⊢
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith [this.1, this.2]
  refine ⟨hr, fun n => (hbounds n).1, fun n => (hbounds n).2, hsum, hdom,
    fun δ hδ => tFullSeq_of_dominates hδ hdom, fun t δ hδ => ?_⟩
  refine bvSeq_of_summable_sq ?_ t hδ
  refine hsum.congr (fun n => ?_)
  have : ((1/2 : ℚ) : ℝ) + r n / 2 - (((1/2 : ℚ) : ℝ) - r n / 2) = r n := by ring
  rw [this, max_eq_right (by positivity)]

/-- **The straddle is essential**: `a ≡ 1`, `e n = 1 − 1/√(n+2)` straddle no rational threshold
infinitely often (`e ↑ 1`), so `BV` holds at every threshold and width, while
`∑ (a − e)² = ∑ 1/(n+2) = ∞` — the "`L²`" slogan is a sufficient condition at a straddled
threshold, not a characterisation.
Source: [[tt-ladder-mandate]] target 8 ("state that as an N+ row so the `L²` slogan is not oversold")
Kind: N+
Fidelity: variant: sequence-level (`a` constant; `e` non-constant)
Hyps: n/a -/
theorem bvSeq_all_not_summable_sq :
    let e : ℕ → ℝ := fun n => 1 - 1 / Real.sqrt ((n : ℝ) + 2)
    (∀ n, e n ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ (t : ℚ) {δ : ℚ}, 0 < δ → BVSeq (fun _ => 1) e t δ) ∧
      ¬ Summable (fun n => (max 0 (1 - e n)) ^ 2) := by
  intro e
  have hsq : ∀ n : ℕ, (0 : ℝ) < Real.sqrt ((n : ℝ) + 2) := fun n => Real.sqrt_pos.2 (by positivity)
  have hs1 : ∀ n : ℕ, (1 : ℝ) ≤ Real.sqrt ((n : ℝ) + 2) := fun n => by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hinv : ∀ n : ℕ, 0 < 1 / Real.sqrt ((n : ℝ) + 2) ∧ 1 / Real.sqrt ((n : ℝ) + 2) ≤ 1 :=
    fun n => ⟨by positivity, by rw [div_le_one (hsq n)]; exact hs1 n⟩
  have hlim : Tendsto (fun n : ℕ => 1 / Real.sqrt ((n : ℝ) + 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 2)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    refine h1.inv_tendsto_atTop.congr (fun n => ?_)
    simp [one_div]
  refine ⟨fun n => ⟨by linarith [(hinv n).2], by linarith [(hinv n).1]⟩, fun t δ hδ => ?_, ?_⟩
  · unfold BVSeq
    rcases le_or_gt (t : ℝ) 1 with ht | ht
    · rcases lt_or_ge (t : ℝ) 1 with ht' | ht'
      · obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 - t
          by linarith)))
        refine summable_of_ne_finset_zero (s := Finset.range N) (fun n hn => ?_)
        have hnN : N ≤ n := not_lt.1 (fun h' => hn (Finset.mem_range.2 h'))
        have := hN n hnN
        rw [(ctsInd_eq_zero_iff hδ _ _).2 (show (t : ℝ) ≤ e n by
          show (t : ℝ) ≤ 1 - 1 / Real.sqrt ((n : ℝ) + 2); linarith), mul_zero]
      · have ht1 : (t : ℝ) = 1 := le_antisymm ht ht'
        refine summable_zero.congr (fun n => ?_)
        rw [(gateSeq_eq_zero_iff hδ _ n).2 (by rw [ht1]), zero_mul]
    · refine summable_zero.congr (fun n => ?_)
      rw [(gateSeq_eq_zero_iff hδ _ n).2 (by show (1 : ℝ) ≤ t; linarith), zero_mul]
  · intro h
    refine not_summable_of_one_div_succ_le (c := 1/2) (by norm_num) (fun n => ?_) h
    have hval : (max 0 (1 - e n)) ^ 2 = 1 / ((n : ℝ) + 2) := by
      show (max 0 (1 - (1 - 1 / Real.sqrt ((n : ℝ) + 2)))) ^ 2 = 1 / ((n : ℝ) + 2)
      rw [show (1 : ℝ) - (1 - 1 / Real.sqrt ((n : ℝ) + 2)) = 1 / Real.sqrt ((n : ℝ) + 2) by ring,
        max_eq_right (hinv n).1.le, div_pow, one_pow, Real.sq_sqrt (by positivity)]
    rw [hval, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]

/-! ## The `L¹` rung at fixed `t` -/

/-- **`BV(t) ↔ T_∀ε(t)` is an `L¹` rung under the solid gate**: for `e n = t − r n` with
`0 ≤ r n ≤ δ` and `r → 0`, against `a ≡ t + δ`: `T_∀ε(t,δ)` holds (indeed `L_cond`), and
`BV(t,δ) ⟺ ∑ r < ∞` (the weight is exactly `r n/δ`). The hypothesis `r n ≤ δ` is needed on
*every* day (it is what makes the ramp linear there). The two sides at the package's width
`(1/2, 1/10)` are `solid_harmonic_witness` (`r = 1/(n+10)`, `T_∀ε ∧ ¬BV`) and `solid_sq_witness`
(`r = 1/(n+10)²`, `T_∀ε ∧ BV`), both below. The package's creep `r = 1/(n+2)` has `r 0 = 1/2 > δ`
and is *not* an instance of this lemma (repair round 2, audit r2 adversarial B1).
Source: [[tt-ladder-mandate]] target 8 (the `L¹` rung)
Kind: P
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem bvSeq_solid_iff {r : ℕ → ℝ} {t δ : ℚ} (hδ : 0 < δ) (hr : ∀ n, 0 ≤ r n ∧ r n ≤ δ)
    (hlim : Tendsto r atTop (𝓝 0)) :
    TAllEpsSeq (fun _ => (t : ℝ) + δ) (fun n => (t : ℝ) - r n) t δ ∧
      (BVSeq (fun _ => (t : ℝ) + δ) (fun n => (t : ℝ) - r n) t δ ↔ Summable r) := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hcond : LCondSeq (fun _ => (t : ℝ) + δ) (fun n => (t : ℝ) - r n) t := by
    intro c hc
    filter_upwards [hlim.eventually (gt_mem_nhds hc)] with n hn _
    show (t : ℝ) - c < t - r n
    linarith
  refine ⟨tAllEpsSeq_of_lCondSeq hδ hcond, ?_⟩
  have hterm : ∀ n, gateSeq t δ (fun _ => (t : ℝ) + δ) n * ctsInd δ (t : ℝ) ((t : ℝ) - r n)
      = r n / δ := by
    intro n
    rw [gateSeq_const_eq_one hδ le_rfl, one_mul, ctsInd_of_le hδ (by linarith [(hr n).1])]
    rw [show (t : ℝ) - ((t : ℝ) - r n) = r n by ring, min_eq_right]
    rw [div_le_one hδR]
    exact (hr n).2
  unfold BVSeq
  simp only [hterm]
  exact summable_div_const_iff hδR.ne'

/-! ### The `L¹` rung's two sides at the package's width

The profiles are indexed through `n + 10` so that `r n ≤ δ = 1/10` holds on day `0` too (creep's
`1/(n+2)` starts at `1/2`). Quote `a ≡ t + δ = 3/5`, threshold `t = 1/2`, width `δ = 1/10`. -/

/-- `1/(n+10) → 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem tendsto_one_div_add_ten : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 10)) atTop (𝓝 0) := by
  have := (tendsto_add_atTop_iff_nat 9).2
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine this.congr (fun n => ?_)
  push_cast
  ring

/-- `1/(n+10)² → 0` (squeezed by `1/(n+10)`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem tendsto_one_div_add_ten_sq :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 10) ^ 2) atTop (𝓝 0) :=
  squeeze_zero (fun n => by positivity)
    (fun n => one_div_le_one_div_of_le (by positivity)
      (by nlinarith [Nat.cast_nonneg (α := ℝ) n]))
    tendsto_one_div_add_ten

/-- `∑ 1/(n+10)² < ∞` (termwise below `1/(n+1)²`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem summable_one_div_add_ten_sq : Summable (fun n : ℕ => 1 / ((n : ℝ) + 10) ^ 2) :=
  summable_one_div_succ_sq.of_nonneg_of_le (fun n => by positivity)
    (fun n => one_div_le_one_div_of_le (by positivity)
      (by nlinarith [Nat.cast_nonneg (α := ℝ) n]))

/-- The profile `1/(n+10)` lies in `[0, 1/10]` on every day — `bvSeq_solid_iff`'s `hr` at
`δ = 1/10`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem one_div_add_ten_mem (n : ℕ) :
    0 ≤ (1 : ℝ) / ((n : ℝ) + 10) ∧ (1 : ℝ) / ((n : ℝ) + 10) ≤ ((1/10 : ℚ) : ℝ) := by
  refine ⟨by positivity, ?_⟩
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- The profile `1/(n+10)²` lies in `[0, 1/10]` on every day — `bvSeq_solid_iff`'s `hr` at
`δ = 1/10`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem one_div_add_ten_sq_mem (n : ℕ) :
    0 ≤ (1 : ℝ) / ((n : ℝ) + 10) ^ 2 ∧ (1 : ℝ) / ((n : ℝ) + 10) ^ 2 ≤ ((1/10 : ℚ) : ℝ) := by
  refine ⟨by positivity, ?_⟩
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- **The `L¹` rung's divergent side, at the package's width**: `t = 1/2`, `δ = 1/10`, the solid
quote `a ≡ t + δ = 3/5`, credence `e n = 1/2 − 1/(n+10)` (profile `r n = 1/(n+10) ≤ δ` on every
day, `r → 0`, `∑ r = ∞`): `T_∀ε(1/2, 1/10)` holds and `BV(1/2, 1/10)` fails. Every hypothesis of
`bvSeq_solid_iff` is inhabited and both of its conclusions are delivered; the `[0,1]` bounds of
both sequences are in the statement. (The package's creep, `r = 1/(n+2)`, is not an instance:
`r 0 = 1/2 > δ`.)
Source: [[tt-ladder-mandate]] target 8 (the `L¹` rung, divergent side); audit r2 adversarial B1
Kind: N+
Fidelity: variant: sequence-level (creep's profile reindexed through `n + 10` so that `r ≤ δ`)
Hyps: n/a -/
theorem solid_harmonic_witness :
    (∀ n, (fun _ : ℕ => ((1/2 : ℚ) : ℝ) + ((1/10 : ℚ) : ℝ)) n ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ n : ℕ, ((1/2 : ℚ) : ℝ) - 1 / ((n : ℝ) + 10) ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ n : ℕ, 0 ≤ (1 : ℝ) / ((n : ℝ) + 10) ∧ (1 : ℝ) / ((n : ℝ) + 10) ≤ ((1/10 : ℚ) : ℝ)) ∧
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 10)) atTop (𝓝 0) ∧
    ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) + 10)) ∧
    TAllEpsSeq (fun _ => ((1/2 : ℚ) : ℝ) + ((1/10 : ℚ) : ℝ))
      (fun n => ((1/2 : ℚ) : ℝ) - 1 / ((n : ℝ) + 10)) (1/2) (1/10) ∧
    ¬ BVSeq (fun _ => ((1/2 : ℚ) : ℝ) + ((1/10 : ℚ) : ℝ))
      (fun n => ((1/2 : ℚ) : ℝ) - 1 / ((n : ℝ) + 10)) (1/2) (1/10) := by
  have hdiv : ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) + 10)) :=
    not_summable_of_one_div_succ_le (c := 1/10) (by norm_num) (fun n => by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n])
  obtain ⟨h1, h2⟩ := bvSeq_solid_iff (t := 1/2) (δ := 1/10) (by norm_num) one_div_add_ten_mem
    tendsto_one_div_add_ten
  refine ⟨fun _ => ?_, fun n => ?_, one_div_add_ten_mem, tendsto_one_div_add_ten, hdiv, h1,
    fun hbv => hdiv (h2.1 hbv)⟩
  · simp only [Set.mem_Icc]
    push_cast
    norm_num
  · have := one_div_add_ten_mem n
    simp only [Set.mem_Icc]
    push_cast at this ⊢
    constructor <;> linarith [this.1, this.2]

/-- **The `L¹` rung's summable side, at the package's width**: same `t = 1/2`, `δ = 1/10`,
quote `a ≡ 3/5`, credence `e n = 1/2 − 1/(n+10)²` (profile `r n = 1/(n+10)² ≤ δ` on every day,
`r → 0`, `∑ r < ∞`): `T_∀ε(1/2, 1/10)` and `BV(1/2, 1/10)` both hold. Every hypothesis of
`bvSeq_solid_iff` is inhabited; the `[0,1]` bounds of both sequences are in the statement.
Source: [[tt-ladder-mandate]] target 8 (the `L¹` rung, summable side); audit r2 adversarial B1
Kind: N+
Fidelity: variant: sequence-level (the `1/(n+1)²` profile reindexed through `n + 10` so that `r ≤ δ`)
Hyps: n/a -/
theorem solid_sq_witness :
    (∀ n, (fun _ : ℕ => ((1/2 : ℚ) : ℝ) + ((1/10 : ℚ) : ℝ)) n ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ n : ℕ, ((1/2 : ℚ) : ℝ) - 1 / ((n : ℝ) + 10) ^ 2 ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ n : ℕ, 0 ≤ (1 : ℝ) / ((n : ℝ) + 10) ^ 2 ∧
      (1 : ℝ) / ((n : ℝ) + 10) ^ 2 ≤ ((1/10 : ℚ) : ℝ)) ∧
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 10) ^ 2) atTop (𝓝 0) ∧
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 10) ^ 2) ∧
    TAllEpsSeq (fun _ => ((1/2 : ℚ) : ℝ) + ((1/10 : ℚ) : ℝ))
      (fun n => ((1/2 : ℚ) : ℝ) - 1 / ((n : ℝ) + 10) ^ 2) (1/2) (1/10) ∧
    BVSeq (fun _ => ((1/2 : ℚ) : ℝ) + ((1/10 : ℚ) : ℝ))
      (fun n => ((1/2 : ℚ) : ℝ) - 1 / ((n : ℝ) + 10) ^ 2) (1/2) (1/10) := by
  obtain ⟨h1, h2⟩ := bvSeq_solid_iff (t := 1/2) (δ := 1/10) (by norm_num) one_div_add_ten_sq_mem
    tendsto_one_div_add_ten_sq
  refine ⟨fun _ => ?_, fun n => ?_, one_div_add_ten_sq_mem, tendsto_one_div_add_ten_sq,
    summable_one_div_add_ten_sq, h1, h2.2 summable_one_div_add_ten_sq⟩
  · simp only [Set.mem_Icc]
    push_cast
    norm_num
  · have := one_div_add_ten_sq_mem n
    simp only [Set.mem_Icc]
    push_cast at this ⊢
    constructor <;> linarith [this.1, this.2]

/-! ## The parked rung -/

/-- **`T(t,ε,δ)` with a parked violation is summable gate mass**: for `e ≡ t − 2ε` and any
`a`, the violation ramp is the positive constant `min 1 (ε/δ)`, so `T(t,ε,δ) ⟺ ∑ G < ∞`.
Source: [[tt-ladder-mandate]] target 8 (the parked rung)
Kind: P
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem tSeq_parked_iff (a : ℕ → ℝ) {t ε δ : ℚ} (hε : 0 < ε) (hδ : 0 < δ) :
    TSeq a (fun _ => (t : ℝ) - 2 * ε) t ε δ ↔ Summable (gateSeq t δ a) := by
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hterm : ∀ n, viol (fun _ => (t : ℝ) - 2 * ε) a t ε δ n =
      gateSeq t δ a n * min 1 ((ε : ℝ) / δ) := by
    intro n
    rw [viol_eq_gateSeq_mul, ctsInd_of_le hδ (by linarith)]
    congr 2
    ring
  have hpos : 0 < min 1 ((ε : ℝ) / δ) := lt_min one_pos (div_pos hεR hδR)
  have hfun : viol (fun _ => (t : ℝ) - 2 * ε) a t ε δ =
      fun n => gateSeq t δ a n * min 1 ((ε : ℝ) / δ) := funext hterm
  unfold TSeq
  rw [hfun]
  exact summable_mul_right_iff hpos.ne'

/-- **`L_prod(t,δ)` with a parked violation is null gate mass**: for `e ≡ t − 2ε` and any `a`,
`L_prod(t,δ) ⟺ G → 0`. With `tSeq_parked_iff`, the rung `L_prod → T(t,ε)` is exactly
"summable versus null gate mass" (W1's `1/log`, W4's `1/(n+1)` versus W2's `1/(n+1)²`).
Width-free (no `0 < δ`): the equivalence holds at every width — at width `0` the gate is
identically `0` and both sides are true; the gate stays in `[0,1]` at any width, so
`lProdSeq_iff_tendsto` applies.
Source: [[tt-ladder-mandate]] target 8 (the parked rung)
Kind: P
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem lProdSeq_parked_iff (a : ℕ → ℝ) {t ε δ : ℚ} (hε : 0 < ε) :
    LProdSeq a (fun _ => (t : ℝ) - 2 * ε) t δ ↔ Tendsto (gateSeq t δ a) atTop (𝓝 0) := by
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  rw [lProdSeq_iff_tendsto]
  have hterm : (fun n => gateSeq t δ a n * max 0 ((t : ℝ) - ((t : ℝ) - 2 * ε))) =
      fun n => gateSeq t δ a n * (2 * ε) := by
    funext n
    rw [show (t : ℝ) - ((t : ℝ) - 2 * ε) = 2 * ε by ring, max_eq_right (by linarith)]
  rw [hterm]
  constructor
  · intro h
    have := h.mul_const (1 / (2 * (ε : ℝ)))
    rw [zero_mul] at this
    refine this.congr (fun n => ?_)
    field_simp
  · intro h
    have := h.mul_const (2 * (ε : ℝ))
    rwa [zero_mul] at this

end Cleanroom.Li.TtLadder
