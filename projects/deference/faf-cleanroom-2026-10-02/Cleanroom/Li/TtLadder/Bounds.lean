import Cleanroom.Li.TtLadder.WitnessesLog
import Cleanroom.Li.TtLadder.WitnessesConst

/-!
# `tt-ladder`: where the standing bounds are load-bearing, and uniformity across thresholds

Repair round 2 of [[tt-ladder-mandate]] (audits r2 fidelity N2/N3, adversarial N2/N3), plus one
result the mandate's target 8 left as a question.

* **`0 ≤ e` is load-bearing for `T ⇒ Avg`** (`avgSeq_needs_lower_bound`): quote `3/5` on even
  days and `sqQuote` on odd days (gate `1` / `1/(n+1)²`), credence `1` on even days and
  `−2(n+1)²` on odd days. `T(1/2, 1/10, 1/10)` holds, the gate mass diverges, and the gated
  average is `≤ 0`, so `Avg(1/2, 1/10, 1/10)` fails. The mirror of `prop_a_needs_lower_bound`
  (F9) for the averaged rung.
* **`0 ≤ e` is load-bearing for `BV ⇒ L_prod`** (`bvSeq_needs_lower_bound`): Prop A's
  counterexample `sqQuote` against `−(n+1)²` also satisfies `BV(1/2, 1/10)`.
* **`a ∈ [0,1]` is load-bearing for both closure `⟹` directions**
  (`closure_needs_quote_bound`): `a n = n`, `e n = n − 1` satisfy `T_full` at every width and
  `L_cond` at every threshold, yet `e` does not dominate `a` (the gap is `1` forever).
* **The threshold range is free under the bounds** (`tFullSeq_iff_Icc`): for `a ≤ 1` and
  `0 ≤ e`, `T_full` over every rational `t` is `T_full` over `t ∈ [0,1]` — for `t ≥ 1` the gate
  is `0`, for `t < 0` the violation ramp is `0`. Off the bounds the negative thresholds carry
  content, which is why the closure theorems (which assume only `a ∈ [0,1]`) take the all-`t`
  form.
* **Uniformity across `t` at the closure** (target 8's "uniform rate across `t`"): under
  dominance, at each margin `ε` the weight vanishes from one day on *uniformly in the
  threshold* (`eventually_viol_eq_zero_forall_t_of_dominates`), so for `a ∈ [0,1]`,
  `T_full(δ) ⟺ ∀ ε > 0, ∀ᶠ n, ∀ t, viol = 0` (`tFullSeq_iff_eventually_zero_forall_t`).
  Uniformity in `(t, ε)` together is a different statement — "eventually no violation at all",
  `∀ᶠ n, a n ≤ e n` (`eventually_viol_eq_zero_forall_iff`) — and W7 fails it on every day
  while satisfying the `t`-uniform form at every width (`w7_uniform_t_not_uniform_eps`).

Over real sequences; nothing here is a theorem about inductors.
-/

namespace Cleanroom.Li.TtLadder

open LogicalInduction Filter Topology Finset
open Cleanroom.Found.LiAsympCalc

/-! ## `0 ≤ e` is load-bearing for `T ⇒ Avg` -/

/-- The mixed quote: solid (`3/5`) on even days, `sqQuote` on odd days.
Source: none: infrastructure (audit r2 adversarial probe R1)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def mixedQuote (n : ℕ) : ℝ := if Even n then 3/5 else sqQuote n

/-- The mixed credence: `1` on even days, `−2(n+1)²` on odd days (unbounded below).
Source: none: infrastructure (audit r2 adversarial probe R1)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def mixedE (n : ℕ) : ℝ := if Even n then 1 else -2 * ((n : ℝ) + 1) ^ 2

/-- The mixed quote's gate at `(1/2, 1/10)`: `1` on even days, `1/(n+1)²` on odd days.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem gateSeq_mixedQuote (n : ℕ) :
    gateSeq (1/2) (1/10) mixedQuote n = if Even n then 1 else 1 / ((n : ℝ) + 1) ^ 2 := by
  by_cases h : Even n
  · simp only [gateSeq, mixedQuote, if_pos h]
    exact gateSeq_const_three_fifths n
  · simp only [gateSeq, mixedQuote, if_neg h]
    exact gateSeq_sqQuote n

/-- Gate times credence for the mixed pair is `3 · altE n − 2` (`+1` on even days, `−2` on odd).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem gateSeq_mixedQuote_mul_mixedE (n : ℕ) :
    gateSeq (1/2) (1/10) mixedQuote n * mixedE n = 3 * altE n - 2 := by
  rw [gateSeq_mixedQuote]
  unfold mixedE altE
  by_cases h : Even n
  · simp only [if_pos h]; norm_num
  · simp only [if_neg h]
    have hn : ((n : ℝ) + 1) ^ 2 ≠ 0 := by positivity
    field_simp
    ring

/-- The mixed pair has summable weight at `(1/2, 1/10, 1/10)`: `0` on even days (`e = 1`),
`≤ 1/(n+1)²` on odd days.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem tSeq_mixed : TSeq mixedQuote mixedE (1/2) (1/10) (1/10) := by
  unfold TSeq
  refine summable_one_div_succ_sq.of_nonneg_of_le (fun n => viol_nonneg _ _ _ _ _ _)
    (fun n => ?_)
  rw [viol_eq_gateSeq_mul, gateSeq_mixedQuote]
  by_cases h : Even n
  · rw [if_pos h]
    have h0 : ctsInd (1/10) (((1/2 : ℚ) : ℝ) - ((1/10 : ℚ) : ℝ)) (mixedE n) = 0 := by
      refine (ctsInd_eq_zero_iff (by norm_num) _ _).2 ?_
      unfold mixedE; rw [if_pos h]; norm_num
    rw [h0, mul_zero]; positivity
  · rw [if_neg h]
    exact mul_le_of_le_one_right (by positivity) (ctsInd_le_one _ _ _)

/-- `altE ≤` the mixed gate termwise.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem altE_le_gateSeq_mixedQuote (n : ℕ) : altE n ≤ gateSeq (1/2) (1/10) mixedQuote n := by
  rw [gateSeq_mixedQuote]; unfold altE
  by_cases h : Even n
  · simp only [if_pos h]; exact le_rfl
  · simp only [if_neg h]; positivity

/-- `prefixSum altE N = ⌈(N+1)/2⌉` (from `sum_altE`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem prefixSum_altE_eq (N : ℕ) : prefixSum altE N = (((N + 1 + 1) / 2 : ℕ) : ℝ) := by
  unfold prefixSum
  rw [sum_altE]

/-- The alternating credence's mass diverges.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem tendsto_prefixSum_altE_atTop : Tendsto (prefixSum altE) atTop atTop := by
  have h1 : Tendsto (fun N : ℕ => (N + 1 + 1) / 2) atTop atTop :=
    tendsto_atTop_atTop.2 (fun b => ⟨2 * b, fun N hN => by omega⟩)
  have h2 : Tendsto (fun N : ℕ => (((N + 1 + 1) / 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp h1
  refine h2.congr (fun N => ?_)
  rw [prefixSum_altE_eq]

/-- The mixed gate's mass diverges (it dominates `altE`'s).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem tendsto_prefixSum_gateSeq_mixedQuote :
    Tendsto (prefixSum (gateSeq (1/2) (1/10) mixedQuote)) atTop atTop :=
  tendsto_atTop_mono (fun N => by
    unfold prefixSum; exact Finset.sum_le_sum (fun i _ => altE_le_gateSeq_mixedQuote i))
    tendsto_prefixSum_altE_atTop

/-- The mixed pair's gated numerator is `3⌈(N+1)/2⌉ − 2(N+1)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem prefixSum_gateSeq_mixedQuote_mul_mixedE (N : ℕ) :
    prefixSum (fun i => gateSeq (1/2) (1/10) mixedQuote i * mixedE i) N
      = 3 * (((N + 1 + 1) / 2 : ℕ) : ℝ) - 2 * ((N : ℝ) + 1) := by
  unfold prefixSum
  rw [Finset.sum_congr rfl (fun i _ => gateSeq_mixedQuote_mul_mixedE i), Finset.sum_sub_distrib,
    ← Finset.mul_sum, sum_altE, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- The mixed pair's gated numerator is `≤ 0` from day `2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem prefixSum_gateSeq_mixedQuote_mul_mixedE_nonpos {N : ℕ} (hN : 2 ≤ N) :
    prefixSum (fun i => gateSeq (1/2) (1/10) mixedQuote i * mixedE i) N ≤ 0 := by
  rw [prefixSum_gateSeq_mixedQuote_mul_mixedE]
  have h : 3 * ((N + 1 + 1) / 2) ≤ 2 * (N + 1) := by omega
  have h' : (3 : ℝ) * (((N + 1 + 1) / 2 : ℕ) : ℝ) ≤ 2 * ((N : ℝ) + 1) := by exact_mod_cast h
  linarith

/-- The mixed gate's mass is positive on every day (day `0` is a solid day).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem prefixSum_gateSeq_mixedQuote_pos (N : ℕ) :
    0 < prefixSum (gateSeq (1/2) (1/10) mixedQuote) N := by
  have h1 : prefixSum altE N ≤ prefixSum (gateSeq (1/2) (1/10) mixedQuote) N := by
    unfold prefixSum; exact Finset.sum_le_sum (fun i _ => altE_le_gateSeq_mixedQuote i)
  have h2 : (1 : ℝ) ≤ prefixSum altE N := by
    rw [prefixSum_altE_eq]
    have : 1 ≤ (N + 1 + 1) / 2 := by omega
    exact_mod_cast this
  linarith

/-- **`T ⇒ Avg` needs the lower bound on the credence**: with `a = mixedQuote` (`[0,1]`-valued,
gate `1` on even days and `1/(n+1)²` on odd days) and `e = mixedE` (`1` on even days,
`−2(n+1)²` on odd days), `T(1/2, 1/10, 1/10)` holds, the gate mass diverges, and the gated
average is `≤ 0` from day `2`, so `Avg(1/2, 1/10, 1/10)` (`≳ₙ 3/10`) fails. The `0 ≤ e` of
`avgSeq_of_tSeq` and `averaged_of_summable` is load-bearing — the averaged-rung mirror of
`prop_a_needs_lower_bound` (F9). Both sequences non-constant; the gate non-constant with
divergent mass.
Source: [[tt-ladder-mandate]] target 2 (iii) / target 4 (finding); audit r1 N-h, audit r2 adversarial N2
Kind: N+
Fidelity: n/a (a counterexample to the unbounded form)
Hyps: n/a -/
theorem avgSeq_needs_lower_bound :
    (∀ n, mixedQuote n ∈ Set.Icc (0 : ℝ) 1) ∧
    TSeq mixedQuote mixedE (1/2) (1/10) (1/10) ∧
    Tendsto (prefixSum (gateSeq (1/2) (1/10) mixedQuote)) atTop atTop ∧
    ¬ AvgSeq mixedQuote mixedE (1/2) (1/10) (1/10) := by
  refine ⟨fun n => ?_, tSeq_mixed, tendsto_prefixSum_gateSeq_mixedQuote, ?_⟩
  · unfold mixedQuote
    split_ifs
    · norm_num
    · exact sqQuote_mem_Icc n
  · intro h
    obtain ⟨N, hN⟩ :=
      eventually_atTop.1 (h tendsto_prefixSum_gateSeq_mixedQuote (1/10) (by norm_num))
    have h1 := hN (N + 2) (by omega)
    have hpos := prefixSum_gateSeq_mixedQuote_pos (N + 2)
    have hnum := prefixSum_gateSeq_mixedQuote_mul_mixedE_nonpos (N := N + 2) (by omega)
    rw [weightedAverage_eq_div hpos.ne'] at h1
    have hle : prefixSum (fun i => gateSeq (1/2) (1/10) mixedQuote i * mixedE i) (N + 2) /
        prefixSum (gateSeq (1/2) (1/10) mixedQuote) (N + 2) ≤ 0 := by
      rw [div_le_iff₀ hpos, zero_mul]; exact hnum
    push_cast at h1
    linarith

/-! ## `0 ≤ e` is load-bearing for `BV ⇒ L_prod` -/

/-- Prop A's counterexample pair also satisfies `BV(1/2, 1/10)`: the weight is `≤ 1/(n+1)²`.
Source: none: infrastructure (audit r2 fidelity probe Q1)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem bvSeq_sqQuote_neg_sq : BVSeq sqQuote (fun n => -((n : ℝ) + 1) ^ 2) (1/2) (1/10) := by
  unfold BVSeq
  refine summable_one_div_succ_sq.of_nonneg_of_le
    (fun n => mul_nonneg (gateSeq_nonneg _ _ _ _) (ctsInd_nonneg _ _ _)) (fun n => ?_)
  rw [gateSeq_sqQuote]
  exact mul_le_of_le_one_right (by positivity) (ctsInd_le_one _ _ _)

/-- **`BV ⇒ L_prod` needs the lower bound on the credence** (and so does `T_∀ε ⇒ L_prod`, in
one package): `sqQuote` (`[0,1]`-valued) against `e n = −(n+1)²` has `BV(1/2, 1/10)` and
`T_∀ε(1/2, 1/10)` and fails `L_prod(1/2, 1/10)`. F9's prose "the same bound is needed by
`BV ⇒ L_prod`" made kernel-visible.
Source: [[tt-ladder-mandate]] target 2 (iv), (vii) (finding F9); audit r2 fidelity N3
Kind: N+
Fidelity: n/a (a counterexample to the unbounded form)
Hyps: n/a -/
theorem bvSeq_needs_lower_bound :
    ∃ a e : ℕ → ℝ, (∀ n, a n ∈ Set.Icc (0 : ℝ) 1) ∧
      BVSeq a e (1/2) (1/10) ∧ TAllEpsSeq a e (1/2) (1/10) ∧ ¬ LProdSeq a e (1/2) (1/10) :=
  ⟨sqQuote, fun n => -((n : ℝ) + 1) ^ 2, sqQuote_mem_Icc, bvSeq_sqQuote_neg_sq,
    tAllEpsSeq_sqQuote_neg_sq, not_lProdSeq_sqQuote_neg_sq⟩

/-! ## `a ∈ [0,1]` is load-bearing for the closure -/

/-- **The closure's `⟹` directions need the bound on the quote**: `a n = n`, `e n = n − 1`
satisfy `T_full(δ)` at every width `δ > 0` (every weight is eventually `0`: from day
`⌈t − ε + 1⌉` the credence exceeds `t − ε`) and `L_cond(t)` at every threshold, yet `e` does not
dominate `a` — the gap `a − e` is `1` forever. So `dominates_of_tFullSeq` and
`dominates_of_lCondSeq_all` cannot drop `a ∈ [0,1]`.
Source: [[tt-ladder-mandate]] target 3 (finding); audit r1 fidelity (prose), audit r2 adversarial N3
Kind: N+
Fidelity: n/a (a counterexample to the unbounded form)
Hyps: n/a -/
theorem closure_needs_quote_bound :
    (∀ δ : ℚ, 0 < δ → TFullSeq (fun n => (n : ℝ)) (fun n => (n : ℝ) - 1) δ) ∧
    (∀ t : ℚ, LCondSeq (fun n => (n : ℝ)) (fun n => (n : ℝ) - 1) t) ∧
    ¬ Dominates (fun n => (n : ℝ) - 1) (fun n => (n : ℝ)) := by
  refine ⟨fun δ hδ t ε hε => ?_, fun t c hc => ?_, fun h => ?_⟩
  · obtain ⟨N, hN⟩ := exists_nat_ge ((t : ℝ) - ε + 1)
    unfold TSeq
    refine summable_of_ne_finset_zero (s := Finset.range N) (fun n hn => ?_)
    have hnN : N ≤ n := not_lt.1 (fun h' => hn (Finset.mem_range.2 h'))
    have hnR : (N : ℝ) ≤ n := by exact_mod_cast hnN
    have h0 : ctsInd δ ((t : ℝ) - ε) ((n : ℝ) - 1) = 0 :=
      (ctsInd_eq_zero_iff hδ _ _).2 (by linarith)
    rw [viol_eq_gateSeq_mul, h0, mul_zero]
  · obtain ⟨N, hN⟩ := exists_nat_ge ((t : ℝ) + 1)
    filter_upwards [eventually_ge_atTop N] with n hn _
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    show (t : ℝ) - c < (n : ℝ) - 1
    linarith
  · obtain ⟨N, hN⟩ := eventually_atTop.1 (h (1/2) (by norm_num))
    have h2 : (N : ℝ) - 1/2 < (N : ℝ) - 1 := hN N le_rfl
    linarith

/-! ## The threshold range is free under the bounds -/

/-- **`T_full` over all rational thresholds is `T_full` over `t ∈ [0,1]`** under the sources'
standing bounds `a ≤ 1`, `0 ≤ e`: for `t ≥ 1` the gate is `0` (`a n ≤ t`), for `t < 0` the
violation ramp is `0` (`t − ε < 0 ≤ e n`). Off these bounds the extra thresholds carry content
(`closure_needs_quote_bound`'s `e` is negative on day `0`; `dominates_of_tFullSeq`'s proof may
pick a negative `t` when `e` is very negative), which is why `TFullSeq` and the closure theorems
take the all-`t` form.
Source: [[fa-positive-results-corrected-v3]] Theorem 1 ("for every rational `t ∈ [0,1]`"); lean-deference-2-001 (`T_full`, "all rational `t, ε`"); audit r2 fidelity N2
Kind: L
Fidelity: exact (the two families coincide under the bounds)
Hyps: n/a -/
theorem tFullSeq_iff_Icc {a e : ℕ → ℝ} (ha : ∀ n, a n ≤ 1) (he : ∀ n, 0 ≤ e n) {δ : ℚ}
    (hδ : 0 < δ) :
    TFullSeq a e δ ↔ ∀ t ε : ℚ, 0 ≤ t → t ≤ 1 → 0 < ε → TSeq a e t ε δ := by
  constructor
  · intro h t ε _ _ hε
    exact h t ε hε
  · intro h t ε hε
    rcases lt_or_ge t 0 with ht | ht
    · unfold TSeq
      refine summable_zero.congr (fun n => ?_)
      rw [viol_eq_gateSeq_mul]
      have htR : (t : ℝ) < 0 := by exact_mod_cast ht
      have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
      rw [(ctsInd_eq_zero_iff hδ _ _).2 (by linarith [he n]), mul_zero]
    rcases le_or_gt t 1 with ht1 | ht1
    · exact h t ε ht ht1 hε
    · unfold TSeq
      refine summable_zero.congr (fun n => ?_)
      rw [viol_eq_gateSeq_mul]
      have ht1R : (1 : ℝ) < t := by exact_mod_cast ht1
      rw [(gateSeq_eq_zero_iff hδ a n).2 (by linarith [ha n]), zero_mul]

/-! ## Uniformity across thresholds at the closure -/

/-- **Under dominance the weight vanishes uniformly in the threshold**: for each margin
`ε > 0` there is one day from which `viol e a t ε δ n = 0` for *every* rational `t`. A positive
weight needs `t < a n` and `e n < t − ε`, hence `a n − e n > ε`; dominance at `c = ε` forbids
that from some day on, whatever `t`. No bounds on `a`, `e`.
Source: [[tt-ladder-mandate]] target 8 ("a uniform rate across `t`", read as: is the day from which the weight vanishes uniform over thresholds?)
Kind: P
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem eventually_viol_eq_zero_forall_t_of_dominates {a e : ℕ → ℝ} (h : Dominates e a)
    {δ : ℚ} (hδ : 0 < δ) {ε : ℚ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ t : ℚ, viol e a t ε δ n = 0 := by
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  filter_upwards [h ε hεR] with n hn t
  rw [viol_eq_gateSeq_mul]
  rcases le_or_gt (a n) t with hat | hat
  · rw [(gateSeq_eq_zero_iff hδ a n).2 hat, zero_mul]
  · rw [(ctsInd_eq_zero_iff hδ _ _).2 (by linarith), mul_zero]

/-- **`T_full` is "eventually zero, uniformly in `t`, at each margin"**: for `a ∈ [0,1]` and
`δ > 0`, `T_full(δ) ⟺ ∀ ε > 0, ∀ᶠ n, ∀ t, viol e a t ε δ n = 0`. Strengthens
`tFullSeq_iff_eventually_zero` (where the day depends on `t`) — the `t`-uniform rate is free at
the closure, so the mandate's first rate question is settled rather than open.
Source: [[tt-ladder-mandate]] target 8 ("a uniform rate across `t`"); lean-deference-2-004
Kind: C
Fidelity: variant: sequence-level (stronger than `tFullSeq_iff_eventually_zero`)
Hyps: (a) none -/
theorem tFullSeq_iff_eventually_zero_forall_t {a e : ℕ → ℝ} (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1)
    {δ : ℚ} (hδ : 0 < δ) :
    TFullSeq a e δ ↔ ∀ ε : ℚ, 0 < ε → ∀ᶠ n in atTop, ∀ t : ℚ, viol e a t ε δ n = 0 :=
  ⟨fun h _ hε =>
    eventually_viol_eq_zero_forall_t_of_dominates (dominates_of_tFullSeq ha hδ h) hδ hε,
   fun h => (tFullSeq_iff_eventually_zero ha hδ).2
    (fun t ε hε => (h ε hε).mono (fun _ hn => hn t))⟩

/-- **Uniformity in `(t, ε)` together is "eventually no violation"**: for `δ > 0`,
`(∀ᶠ n, ∀ t ε > 0, viol e a t ε δ n = 0) ⟺ ∀ᶠ n, a n ≤ e n`. If `e n < a n` on a day, a rational
margin `ε < (a n − e n)/2` and a rational threshold `t ∈ (e n + ε, a n)` give a positive weight
that day. No bounds on `a`, `e`.
Source: [[tt-ladder-mandate]] target 8 (the `(t, ε)`-uniform reading of "a uniform rate")
Kind: P
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem eventually_viol_eq_zero_forall_iff {a e : ℕ → ℝ} {δ : ℚ} (hδ : 0 < δ) :
    (∀ᶠ n in atTop, ∀ t ε : ℚ, 0 < ε → viol e a t ε δ n = 0) ↔ ∀ᶠ n in atTop, a n ≤ e n := by
  constructor
  · refine fun h => h.mono (fun n hn => ?_)
    by_contra hlt
    push Not at hlt
    obtain ⟨ε, hε0, hε⟩ := exists_rat_btwn (show (0 : ℝ) < (a n - e n) / 2 by linarith)
    obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn (show e n + ε < a n by linarith)
    have hz := hn t ε (by exact_mod_cast hε0)
    rw [viol_eq_gateSeq_mul] at hz
    have hg : 0 < gateSeq t δ a n := (gateSeq_pos_iff hδ a n).2 ht2
    have hr : 0 < ctsInd δ ((t : ℝ) - ε) (e n) := (ctsInd_pos_iff hδ _ _).2 (by linarith)
    exact absurd hz (mul_pos hg hr).ne'
  · refine fun h => h.mono (fun n hn t ε hε => ?_)
    rw [viol_eq_gateSeq_mul]
    rcases le_or_gt (a n) t with hat | hat
    · rw [(gateSeq_eq_zero_iff hδ a n).2 hat, zero_mul]
    · have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
      rw [(ctsInd_eq_zero_iff hδ _ _).2 (by linarith), mul_zero]

/-- W7's quote exceeds its credence on every day (`w7Decay n > 0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem w7E_lt_w7Quote (n : ℕ) : w7E n < w7Quote n := by
  have : 0 < w7Decay n := by
    unfold w7Decay
    exact div_pos (by norm_num) (sqrt_log_add_two_pos n)
  unfold w7Quote w7E
  linarith

/-- **W7 separates the two uniformities**: at every width, at each margin the weight vanishes
from one day on uniformly in `t` (dominance), but there is no day from which it vanishes for
all `(t, ε)` at once — W7's quote exceeds its credence on every day. So the `t`-uniform form is
the closure's, and the `(t, ε)`-uniform form is strictly stronger.
Source: [[tt-ladder-mandate]] target 8; lean-deference-2-003 (W7)
Kind: N+
Fidelity: variant: sequence-level
Hyps: n/a -/
theorem w7_uniform_t_not_uniform_eps :
    (∀ δ : ℚ, 0 < δ → ∀ ε : ℚ, 0 < ε →
      ∀ᶠ n in atTop, ∀ t : ℚ, viol w7E w7Quote t ε δ n = 0) ∧
    ∀ δ : ℚ, 0 < δ → ¬ ∀ᶠ n in atTop, ∀ t ε : ℚ, 0 < ε → viol w7E w7Quote t ε δ n = 0 :=
  ⟨fun δ hδ ε hε => eventually_viol_eq_zero_forall_t_of_dominates dominates_w7 hδ hε,
   fun δ hδ h => by
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((eventually_viol_eq_zero_forall_iff hδ).1 h)
    exact absurd (hN N le_rfl) (not_le.2 (w7E_lt_w7Quote N))⟩

end Cleanroom.Li.TtLadder
