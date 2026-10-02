import Cleanroom.Corrigibility.CorrLiShutdown.SignedError
import Mathlib.Data.Nat.Sqrt

/-!
# `corr-li-shutdown` — Drift (T6): the trichotomy's two-sided package is inhabited, in its first
two cases — PROVED (repair round 3)

Audit r3 adversarial B1: `signedError_trichotomy`'s docstring said its first two cases were
realized by `signedError_two_sided_refuted`'s instance and its mirror. They are not: that
instance (`price ≡ 1/2`, `truth ≡ 1`) violates the trichotomy's *downward* clause — its downward
ramps `Ind_{η'}(−T_N > M')` are eventually `1`, divergent, and average `truth ≡ 1` to `1 ≠ 1/2`.
What realizes case 1 (`T → −∞`) under **both** clauses is F11's drift instance, previously
argued only. This module builds it.

* **The barrier walk** `driftExcess`: `D_0 := 1`, `D_{N+1} := D_N + 1` if `D_N < ⌊√(N+1)⌋`, else
  `D_N − 1`; **the drift stream** `driftTruth` is the Boolean stream it drives (`truth_0 := 1`,
  `truth_{N+1} := 1` exactly when the walk steps up). So `∑_{i ≤ N} (2·truth_i − 1) = D_N`
  (`driftExcess_succ`) and, at `price ≡ 1/2`, the realized signed error has running sum
  `T_N = −D_N/2` (`prefixSum_driftError`).
* **The walk hugs the barrier**: `⌊√N⌋ − 1 ≤ D_N ≤ ⌊√N⌋ + 1` (`driftExcess_bounds`), because
  the barrier grows by at most one per day (`Nat.sqrt_succ_le_succ_sqrt`). Hence `T → −∞` and
  `T` is bounded above (`driftT_tendsto_atBot`, `driftT_bddAbove`), while `D_N = o(N)` makes the
  truth density `1/2` (`tendsto_prefixSum_driftTruth_div`).
* **The clauses.** Upward: every upward ramp of a running sum tending to `−∞` is eventually `0`
  (`runningSumRamp_eventually_zero_of_tendsto_atBot`), so none diverges and the clause holds
  vacuously — as it must in case 1. Downward: every downward ramp is eventually `1`
  (`runningSumRamp_eventually_one_of_tendsto_atTop`), and the weighted average under a
  nonnegative weighting that is eventually `1` is the Cesàro mean
  (`weightedAverage_tendsto_of_eventually_one`), which is `1/2`: the clause holds **with content**.
* **Headlines.** `signedError_trichotomy_atBot_realized` (N+): the trichotomy's full two-sided
  package at `price ≡ 1/2`, `truth := driftTruth`, `p = 1/2`, together with `T → −∞` and `T`
  bounded above (case 1, and not case 3). `signedError_trichotomy_atTop_realized`: the mirror
  `truth ↦ 1 − truth` (case 2). `signedError_trichotomy_at_drift`: the trichotomy applied to the
  package (the hypotheses are in its exact shape).

**Not built — case 3** (unbounded on both sides under both clauses): argued only. An i.i.d.
Bernoulli(`1/2`) stream priced at `1/2` has it almost surely (recurrence of the simple random
walk); the block-alternating stream `truth = 1` on `[k², (k+1)²)` for even `k`, `0` for odd `k`,
has it deterministically (`T` oscillates with amplitude `~√N/2`), but its ramp-weighted averages
need a within-block count of the days with `T_N > M'` that is beyond this round.

**Disclosure on the grade.** The instance is deterministic and non-constant (density `1/2`, by
`tendsto_prefixSum_driftTruth_div`); the downward clause is exercised with content; the upward
clause holds vacuously, which is forced by the conclusion (`T → −∞`) and not an artifact of the
instance. It is excluded by Def. 4.4.1 exactly as F11 says: the weighting "`1` at the days the
walk steps up" reads `truth` itself.
-/

namespace Cleanroom.Corrigibility.CorrLiShutdown

open LogicalInduction Cleanroom.Found.LiAsympCalc
open Filter Topology

/-! ## A. Ramps of a divergent running sum -/

/-- If the running sum tends to `−∞`, every upward ramp of it is eventually `0`
(`T_N ≤ M'` eventually). Generalizes `runningSumRamp_const_eventually_zero`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma runningSumRamp_eventually_zero_of_tendsto_atBot {e : ℕ → ℝ}
    (he : Tendsto (prefixSum e) atTop atBot) (η' M' : ℚ) (hη' : 0 < η') (N₀ : ℕ) :
    ∀ᶠ n in atTop, runningSumRamp e η' M' N₀ n = 0 := by
  obtain ⟨K, hK⟩ := tendsto_atTop_atBot.mp he (M' : ℝ)
  filter_upwards [eventually_ge_atTop (K + 1)] with n hn
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  simp only [runningSumRamp]
  split_ifs with h
  · exact (ctsInd_eq_zero_iff hη' _ _).2 (hK N (by omega))
  · rfl

/-- If the running sum tends to `+∞`, every ramp of it is eventually `1`
(`T_N ≥ M' + η'` eventually, past the cutoff `N₀`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma runningSumRamp_eventually_one_of_tendsto_atTop {e : ℕ → ℝ}
    (he : Tendsto (prefixSum e) atTop atTop) (η' M' : ℚ) (hη' : 0 < η') (N₀ : ℕ) :
    ∀ᶠ n in atTop, runningSumRamp e η' M' N₀ n = 1 := by
  obtain ⟨K, hK⟩ := tendsto_atTop_atTop.mp he ((M' : ℝ) + η')
  filter_upwards [eventually_ge_atTop (max K N₀ + 1)] with n hn
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hN₀ : N₀ ≤ N := by have := le_max_right K N₀; omega
  have hKN : K ≤ N := by have := le_max_left K N₀; omega
  simp only [runningSumRamp]
  rw [if_pos hN₀, ctsInd_eq_one_iff hη']
  have := hK N hKN
  linarith

/-- A weighting that is eventually `0` has eventually constant prefix sums, hence is not
divergent. Generalizes `runningSumRamp_const_not_divergent`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma not_tendsto_prefixSum_atTop_of_eventually_zero {w : ℕ → ℝ}
    (hw : ∀ᶠ n in atTop, w n = 0) : ¬ Tendsto (prefixSum w) atTop atTop := by
  intro htend
  obtain ⟨K, hK⟩ := hw.exists_forall_of_atTop
  have hconst : ∀ n, K ≤ n → prefixSum w n = prefixSum w K := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ m hm ih => rw [prefixSum_succ, hK (m + 1) (by omega), add_zero, ih]
  obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp htend (prefixSum w K + 1)
  have h1 := hN (max N K) (le_max_left _ _)
  rw [hconst (max N K) (le_max_right _ _)] at h1
  linarith

/-! ## B. Weighted averages under an eventually-`1` weighting are Cesàro means -/

/-- Under a nonnegative weighting that is eventually `1`, the weighted average of `t` has the
limit of the plain Cesàro mean `(∑_{i ≤ N} t_i)/(N + 1)`: past the day `K` from which the
weighting is `1`, numerator and denominator differ from the Cesàro mean's by constants.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma weightedAverage_tendsto_of_eventually_one {w t : ℕ → ℝ} {L : ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∀ᶠ n in atTop, w n = 1)
    (ht : Tendsto (fun N : ℕ => prefixSum t N / ((N : ℝ) + 1)) atTop (𝓝 L)) :
    weightedAverage w t ≈ₙ fun _ => L := by
  obtain ⟨K, hK⟩ := hw1.exists_forall_of_atTop
  set c₁ := prefixSum (fun i => w i * t i) K - prefixSum t K with hc₁
  set c₂ := prefixSum w K - ((K : ℝ) + 1) with hc₂
  have hnum : ∀ N, K ≤ N → prefixSum (fun i => w i * t i) N = prefixSum t N + c₁ := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => rw [hc₁]; ring
    | succ m hm ih =>
      rw [prefixSum_succ, prefixSum_succ t, ih, hK (m + 1) (by omega), one_mul]; ring
  have hden : ∀ N, K ≤ N → prefixSum w N = ((N : ℝ) + 1) + c₂ := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => rw [hc₂]; ring
    | succ m hm ih =>
      rw [prefixSum_succ, ih, hK (m + 1) (by omega)]; push_cast; ring
  have hpos : ∀ N, K < N → 0 < prefixSum w N := by
    intro N hN
    rw [hden N hN.le, hc₂]
    have h0 := prefixSum_nonneg hw0 K
    have hKN : (K : ℝ) + 1 ≤ N := by exact_mod_cast Nat.lt_iff_add_one_le.mp hN
    linarith
  have hinv : ∀ c : ℝ, Tendsto (fun N : ℕ => c / ((N : ℝ) + 1)) atTop (𝓝 0) := fun c =>
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have heq : (fun N => weightedAverage w t N - L) =ᶠ[atTop]
      fun N => (prefixSum t N / ((N : ℝ) + 1) + c₁ / ((N : ℝ) + 1)) /
        (1 + c₂ / ((N : ℝ) + 1)) - L := by
    filter_upwards [eventually_gt_atTop K] with N hN
    have hd : (N : ℝ) + 1 + c₂ ≠ 0 := by
      have := hpos N hN
      rw [hden N hN.le] at this
      exact this.ne'
    rw [weightedAverage_eq_div (hpos N hN).ne', hnum N hN.le, hden N hN.le]
    have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
    congr 1
    field_simp
  unfold AsympEq
  have hlim : Tendsto (fun N : ℕ => (prefixSum t N / ((N : ℝ) + 1) + c₁ / ((N : ℝ) + 1)) /
      (1 + c₂ / ((N : ℝ) + 1)) - L) atTop (𝓝 0) := by
    have h1 := ht.add (hinv c₁)
    have h2 := (tendsto_const_nhds (x := (1 : ℝ))).add (hinv c₂)
    have h3 := (h1.div h2 (by norm_num)).sub (tendsto_const_nhds (x := L))
    simpa using h3
  exact hlim.congr' heq.symm

/-! ## C. The barrier walk and the drift stream -/

/-- **The barrier walk** `D_0 := 1`, `D_{N+1} := D_N + 1` if `D_N < ⌊√(N+1)⌋`, else `D_N − 1`:
the excess of ones over zeros of the drift stream through day `N`.
Source: [[corr-li-shutdown-findings]] F11 (the barrier recursion `truth_N := 1[T_{N−1} > −√N]`, written on the excess `D = −2T`)
Kind: D
Fidelity: n/a -/
def driftExcess : ℕ → ℤ
  | 0 => 1
  | N + 1 => driftExcess N + (if driftExcess N < (Nat.sqrt (N + 1) : ℤ) then 1 else -1)

/-- **The drift stream**: `truth_0 := 1`, `truth_{N+1} := 1` exactly when the barrier walk steps
up at day `N + 1`. A Boolean stream with density `1/2` and a divergent excess of ones.
Source: [[corr-li-shutdown-findings]] F11 (the drift instance)
Kind: D
Fidelity: n/a -/
noncomputable def driftTruth : ℕ → ℝ
  | 0 => 1
  | N + 1 => if driftExcess N < (Nat.sqrt (N + 1) : ℤ) then 1 else 0

/-- The drift stream is Boolean.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma driftTruth_boolean (i : ℕ) : driftTruth i = 0 ∨ driftTruth i = 1 := by
  cases i with
  | zero => exact Or.inr rfl
  | succ N =>
    simp only [driftTruth]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- The walk's step is `2·truth_{N+1} − 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma driftExcess_succ (N : ℕ) :
    (driftExcess (N + 1) : ℝ) = driftExcess N + (2 * driftTruth (N + 1) - 1) := by
  simp only [driftExcess, driftTruth]
  split_ifs <;> push_cast <;> ring

/-- `∑_{i ≤ N} truth_i = ((N + 1) + D_N)/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prefixSum_driftTruth (N : ℕ) :
    prefixSum driftTruth N = (((N : ℝ) + 1) + driftExcess N) / 2 := by
  induction N with
  | zero => simp [prefixSum_zero, driftTruth, driftExcess]
  | succ N ih =>
    rw [prefixSum_succ, ih, driftExcess_succ]
    push_cast
    ring

/-- At `price ≡ 1/2` the running sum of the realized signed error is `T_N = −D_N/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prefixSum_driftError (N : ℕ) :
    prefixSum (fun i => (1 / 2 : ℝ) - driftTruth i) N = -(driftExcess N : ℝ) / 2 := by
  induction N with
  | zero => simp [prefixSum_zero, driftTruth, driftExcess]; norm_num
  | succ N ih =>
    rw [prefixSum_succ, ih, driftExcess_succ]
    ring

/-- **The walk hugs the barrier**: `⌊√N⌋ − 1 ≤ D_N ≤ ⌊√N⌋ + 1`, because the barrier is monotone
and grows by at most one per day.
Source: [[corr-li-shutdown-findings]] F11
Kind: P
Fidelity: n/a -/
lemma driftExcess_bounds (N : ℕ) :
    (Nat.sqrt N : ℤ) - 1 ≤ driftExcess N ∧ driftExcess N ≤ (Nat.sqrt N : ℤ) + 1 := by
  induction N with
  | zero => simp [driftExcess]
  | succ N ih =>
    have hmono : (Nat.sqrt N : ℤ) ≤ Nat.sqrt (N + 1) := by
      exact_mod_cast Nat.sqrt_le_sqrt (Nat.le_succ N)
    have hstep : (Nat.sqrt (N + 1) : ℤ) ≤ Nat.sqrt N + 1 := by
      exact_mod_cast Nat.sqrt_succ_le_succ_sqrt N
    simp only [driftExcess]
    split_ifs with h <;> omega

/-- `⌊√N⌋ → ∞`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tendsto_natSqrt_atTop : Tendsto (fun N : ℕ => (Nat.sqrt N : ℝ)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨⌈b⌉₊ ^ 2, fun N hN => ?_⟩
  have h1 : ⌈b⌉₊ ≤ Nat.sqrt N := Nat.le_sqrt'.2 hN
  calc b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
    _ ≤ (Nat.sqrt N : ℝ) := by exact_mod_cast h1

/-- `⌊√N⌋/(N + 1) → 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tendsto_natSqrt_div :
    Tendsto (fun N : ℕ => (Nat.sqrt N : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) := by
  have hbound : ∀ N : ℕ, (Nat.sqrt N : ℝ) / ((N : ℝ) + 1) ≤ 1 / (Nat.sqrt N : ℝ) := by
    intro N
    rcases Nat.eq_zero_or_pos (Nat.sqrt N) with h | h
    · rw [h]; simp
    · have hpos : (0 : ℝ) < Nat.sqrt N := by exact_mod_cast h
      have hsq : (Nat.sqrt N : ℝ) * Nat.sqrt N ≤ (N : ℝ) + 1 := by
        have h' : ((Nat.sqrt N * Nat.sqrt N : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sqrt_le N
        push_cast at h'
        linarith
      calc (Nat.sqrt N : ℝ) / ((N : ℝ) + 1)
          ≤ (Nat.sqrt N : ℝ) / ((Nat.sqrt N : ℝ) * Nat.sqrt N) :=
            div_le_div_of_nonneg_left hpos.le (by positivity) hsq
        _ = 1 / (Nat.sqrt N : ℝ) := by
            rw [div_mul_eq_div_div, div_self hpos.ne']
  have hnonneg : ∀ N : ℕ, 0 ≤ (Nat.sqrt N : ℝ) / ((N : ℝ) + 1) := fun N => by positivity
  have hinv : Tendsto (fun N : ℕ => 1 / (Nat.sqrt N : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp tendsto_natSqrt_atTop
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv hnonneg hbound

/-- `D_N/(N + 1) → 0`: the excess is `o(N)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tendsto_driftExcess_div :
    Tendsto (fun N : ℕ => (driftExcess N : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hlow : Tendsto (fun N : ℕ => (Nat.sqrt N : ℝ) / ((N : ℝ) + 1) - 1 / ((N : ℝ) + 1))
      atTop (𝓝 0) := by
    simpa using tendsto_natSqrt_div.sub hinv
  have hhigh : Tendsto (fun N : ℕ => (Nat.sqrt N : ℝ) / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1))
      atTop (𝓝 0) := by
    simpa using tendsto_natSqrt_div.add hinv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hhigh (fun N => ?_) (fun N => ?_)
  · have h' : (Nat.sqrt N : ℝ) - 1 ≤ driftExcess N := by exact_mod_cast (driftExcess_bounds N).1
    rw [← sub_div]
    exact div_le_div_of_nonneg_right h' (by positivity)
  · have h' : (driftExcess N : ℝ) ≤ Nat.sqrt N + 1 := by exact_mod_cast (driftExcess_bounds N).2
    rw [← add_div]
    exact div_le_div_of_nonneg_right h' (by positivity)

/-- **The drift stream has density `1/2`**: its Cesàro mean tends to `1/2`.
Source: [[corr-li-shutdown-findings]] F11
Kind: P
Fidelity: n/a -/
lemma tendsto_prefixSum_driftTruth_div :
    Tendsto (fun N : ℕ => prefixSum driftTruth N / ((N : ℝ) + 1)) atTop (𝓝 (1 / 2)) := by
  have heq : (fun N : ℕ => prefixSum driftTruth N / ((N : ℝ) + 1)) =
      fun N : ℕ => 1 / 2 + (driftExcess N : ℝ) / ((N : ℝ) + 1) / 2 := by
    funext N
    rw [prefixSum_driftTruth]
    have : ((N : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rw [heq]
  have := (tendsto_driftExcess_div.div_const 2).const_add (1 / 2 : ℝ)
  simpa using this

/-- **`T → −∞`** at the drift instance: `T_N = −D_N/2 ≤ −(⌊√N⌋ − 1)/2`.
Source: [[corr-li-shutdown-findings]] F11
Kind: P
Fidelity: n/a -/
lemma driftT_tendsto_atBot :
    Tendsto (prefixSum (fun i => (1 / 2 : ℝ) - driftTruth i)) atTop atBot := by
  rw [show prefixSum (fun i => (1 / 2 : ℝ) - driftTruth i) = fun N => -(driftExcess N : ℝ) / 2
    from funext prefixSum_driftError]
  rw [tendsto_atTop_atBot]
  intro b
  obtain ⟨K, hK⟩ := tendsto_atTop_atTop.mp tendsto_natSqrt_atTop (-2 * b + 1)
  refine ⟨K, fun N hN => ?_⟩
  have h1 := hK N hN
  have h2 : (Nat.sqrt N : ℝ) - 1 ≤ driftExcess N := by exact_mod_cast (driftExcess_bounds N).1
  linarith

/-- `T` is bounded above (by `1/2`) at the drift instance: case 1 of the trichotomy, not case 3.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma driftT_bddAbove :
    BddAbove (Set.range (prefixSum (fun i => (1 / 2 : ℝ) - driftTruth i))) := by
  refine ⟨1 / 2, ?_⟩
  rintro _ ⟨N, rfl⟩
  rw [prefixSum_driftError]
  have h : (Nat.sqrt N : ℝ) - 1 ≤ driftExcess N := by exact_mod_cast (driftExcess_bounds N).1
  have h0 : (0 : ℝ) ≤ Nat.sqrt N := Nat.cast_nonneg _
  linarith

/-- The running sum of the *negated* error, `∑_{i ≤ N} (truth_i − 1/2) = D_N/2`, tends to `+∞`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma driftTdown_tendsto_atTop :
    Tendsto (prefixSum (fun i => driftTruth i - (1 / 2 : ℝ))) atTop atTop := by
  have hfun : (fun i => driftTruth i - (1 / 2 : ℝ)) = fun i => -((1 / 2 : ℝ) - driftTruth i) := by
    funext i; ring
  rw [hfun, show prefixSum (fun i => -((1 / 2 : ℝ) - driftTruth i)) =
      fun N => -prefixSum (fun i => (1 / 2 : ℝ) - driftTruth i) N from funext (prefixSum_neg _)]
  exact tendsto_neg_atBot_atTop.comp driftT_tendsto_atBot

/-! ## D. The two clauses at the drift instance -/

/-- **The upward clause holds (vacuously)** at the drift instance: `T → −∞`, so no upward ramp
diverges.
Source: [[corr-li-shutdown-findings]] F11
Kind: L
Fidelity: n/a -/
lemma drift_upward_clause (η' M' : ℚ) (N₀ : ℕ) (hη' : 0 < η')
    (htend : Tendsto (prefixSum (runningSumRamp (fun i => (1 / 2 : ℝ) - driftTruth i) η' M' N₀))
      atTop atTop) :
    weightedAverage (runningSumRamp (fun i => (1 / 2 : ℝ) - driftTruth i) η' M' N₀) driftTruth ≈ₙ
      fun _ => (1 / 2 : ℝ) :=
  absurd htend (not_tendsto_prefixSum_atTop_of_eventually_zero
    (runningSumRamp_eventually_zero_of_tendsto_atBot driftT_tendsto_atBot η' M' hη' N₀))

/-- **The downward clause holds with content** at the drift instance: every downward ramp
`Ind_{η'}(−T_N > M')` is eventually `1`, and it averages the drift stream to its density `1/2`.
Source: [[corr-li-shutdown-findings]] F11
Kind: C
Fidelity: n/a -/
lemma drift_downward_clause (η' M' : ℚ) (N₀ : ℕ) (hη' : 0 < η') :
    weightedAverage (runningSumRamp (fun i => driftTruth i - (1 / 2 : ℝ)) η' M' N₀) driftTruth ≈ₙ
      fun _ => (1 / 2 : ℝ) :=
  weightedAverage_tendsto_of_eventually_one (fun i => (runningSumRamp_mem _ _ _ _ i).1)
    (runningSumRamp_eventually_one_of_tendsto_atTop driftTdown_tendsto_atTop η' M' hη' N₀)
    tendsto_prefixSum_driftTruth_div

/-- **The trichotomy's two-sided package is inhabited, in its first case** (N+): at `price ≡ 1/2`,
`truth := driftTruth`, `p = 1/2`, every hypothesis of `signedError_trichotomy` holds — the upward
clause vacuously (forced by `T → −∞`), the downward clause with content (its ramps are
eventually `1` and average the stream to its density `1/2`) — and `T → −∞` with `T` bounded above.
This is F11's drift instance, machine-checked (audit r3 adversarial B1); it is excluded by
Def. 4.4.1 through a weighting that reads `truth` itself (F11).
Source: [[corr-li-shutdown-findings]] F11; audit r3 adversarial B1 (option (iii))
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem signedError_trichotomy_atBot_realized :
    (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 ∧
    Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2)) ∧
    (∀ i, driftTruth i = 0 ∨ driftTruth i = 1) ∧
    (∀ (η' M' : ℚ) (N₀ : ℕ), 0 < η' →
      Tendsto (prefixSum (runningSumRamp (fun i => (1 / 2 : ℝ) - driftTruth i) η' M' N₀))
        atTop atTop →
      weightedAverage (runningSumRamp (fun i => (1 / 2 : ℝ) - driftTruth i) η' M' N₀)
        driftTruth ≈ₙ fun _ => (1 / 2 : ℝ)) ∧
    (∀ (η' M' : ℚ) (N₀ : ℕ), 0 < η' →
      Tendsto (prefixSum (runningSumRamp (fun i => driftTruth i - (1 / 2 : ℝ)) η' M' N₀))
        atTop atTop →
      weightedAverage (runningSumRamp (fun i => driftTruth i - (1 / 2 : ℝ)) η' M' N₀)
        driftTruth ≈ₙ fun _ => (1 / 2 : ℝ)) ∧
    Tendsto (prefixSum (fun i => (1 / 2 : ℝ) - driftTruth i)) atTop atBot ∧
    BddAbove (Set.range (prefixSum (fun i => (1 / 2 : ℝ) - driftTruth i))) :=
  ⟨by norm_num, by norm_num, tendsto_const_nhds, driftTruth_boolean,
   fun η' M' N₀ hη' htend => drift_upward_clause η' M' N₀ hη' htend,
   fun η' M' N₀ hη' _ => drift_downward_clause η' M' N₀ hη',
   driftT_tendsto_atBot, driftT_bddAbove⟩

/-- The trichotomy applied to the drift instance — the package above is in the exact shape of
`signedError_trichotomy`'s hypotheses at `price := fun _ => 1/2`, `truth := driftTruth`.
Source: none: infrastructure (shape check)
Kind: L
Fidelity: n/a -/
theorem signedError_trichotomy_at_drift :
    Tendsto (prefixSum (fun i => (1 / 2 : ℝ) - driftTruth i)) atTop atBot ∨
      Tendsto (prefixSum (fun i => (1 / 2 : ℝ) - driftTruth i)) atTop atTop ∨
      (¬ BddAbove (Set.range (prefixSum (fun i => (1 / 2 : ℝ) - driftTruth i))) ∧
        ¬ BddBelow (Set.range (prefixSum (fun i => (1 / 2 : ℝ) - driftTruth i)))) :=
  signedError_trichotomy (price := fun _ => (1 / 2 : ℝ)) (truth := driftTruth) (p := 1 / 2)
    (by norm_num) (by norm_num) tendsto_const_nhds driftTruth_boolean
    signedError_trichotomy_atBot_realized.2.2.2.2.1
    signedError_trichotomy_atBot_realized.2.2.2.2.2.1

/-! ## E. The mirror: case 2 -/

/-- The complemented drift stream is Boolean.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma one_sub_driftTruth_boolean (i : ℕ) :
    (1 - driftTruth i) = 0 ∨ (1 - driftTruth i) = 1 := by
  rcases driftTruth_boolean i with h | h <;> rw [h] <;> norm_num

/-- `∑_{i ≤ N} (1 − truth_i) = (N + 1) − ∑_{i ≤ N} truth_i`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prefixSum_one_sub_driftTruth (N : ℕ) :
    prefixSum (fun i => 1 - driftTruth i) N = ((N : ℝ) + 1) - prefixSum driftTruth N := by
  induction N with
  | zero => simp [prefixSum_zero]
  | succ N ih =>
    rw [prefixSum_succ, prefixSum_succ driftTruth, ih]
    push_cast
    ring

/-- The complemented drift stream also has density `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tendsto_prefixSum_one_sub_driftTruth_div :
    Tendsto (fun N : ℕ => prefixSum (fun i => 1 - driftTruth i) N / ((N : ℝ) + 1)) atTop
      (𝓝 (1 / 2)) := by
  have heq : (fun N : ℕ => prefixSum (fun i => 1 - driftTruth i) N / ((N : ℝ) + 1)) =
      fun N : ℕ => 1 - prefixSum driftTruth N / ((N : ℝ) + 1) := by
    funext N
    rw [prefixSum_one_sub_driftTruth]
    have : ((N : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rw [heq]
  have := tendsto_prefixSum_driftTruth_div.const_sub (1 : ℝ)
  convert this using 2
  norm_num

/-- At the mirror instance the running sum is `+D_N/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prefixSum_driftMirrorError :
    prefixSum (fun i => (1 / 2 : ℝ) - (1 - driftTruth i)) =
      fun N => (driftExcess N : ℝ) / 2 := by
  funext N
  have hfun : (fun i => (1 / 2 : ℝ) - (1 - driftTruth i)) =
      fun i => -((1 / 2 : ℝ) - driftTruth i) := by
    funext i; ring
  rw [hfun, prefixSum_neg, prefixSum_driftError]
  ring

/-- **The mirror upward clause holds with content**: the upward ramps of the mirror's running sum
are the downward ramps of the original, eventually `1`, averaging `1 − truth` to `1/2`.
Source: [[corr-li-shutdown-findings]] F11 (mirror)
Kind: C
Fidelity: n/a -/
lemma driftMirror_upward_clause (η' M' : ℚ) (N₀ : ℕ) (hη' : 0 < η') :
    weightedAverage (runningSumRamp (fun i => (1 / 2 : ℝ) - (1 - driftTruth i)) η' M' N₀)
      (fun i => 1 - driftTruth i) ≈ₙ fun _ => (1 / 2 : ℝ) := by
  have hfun : (fun i => (1 / 2 : ℝ) - (1 - driftTruth i)) = fun i => driftTruth i - 1 / 2 := by
    funext i; ring
  rw [hfun]
  exact weightedAverage_tendsto_of_eventually_one (fun i => (runningSumRamp_mem _ _ _ _ i).1)
    (runningSumRamp_eventually_one_of_tendsto_atTop driftTdown_tendsto_atTop η' M' hη' N₀)
    tendsto_prefixSum_one_sub_driftTruth_div

/-- **The mirror downward clause holds (vacuously)**: its ramps are the upward ramps of the
original, eventually `0`.
Source: [[corr-li-shutdown-findings]] F11 (mirror)
Kind: L
Fidelity: n/a -/
lemma driftMirror_downward_clause (η' M' : ℚ) (N₀ : ℕ) (hη' : 0 < η')
    (htend : Tendsto (prefixSum (runningSumRamp (fun i => (1 - driftTruth i) - (1 / 2 : ℝ))
      η' M' N₀)) atTop atTop) :
    weightedAverage (runningSumRamp (fun i => (1 - driftTruth i) - (1 / 2 : ℝ)) η' M' N₀)
      (fun i => 1 - driftTruth i) ≈ₙ fun _ => (1 / 2 : ℝ) := by
  have hfun : (fun i => (1 - driftTruth i) - (1 / 2 : ℝ)) =
      fun i => (1 / 2 : ℝ) - driftTruth i := by
    funext i; ring
  rw [hfun] at htend
  exact absurd htend (not_tendsto_prefixSum_atTop_of_eventually_zero
    (runningSumRamp_eventually_zero_of_tendsto_atBot driftT_tendsto_atBot η' M' hη' N₀))

/-- **The trichotomy's two-sided package is inhabited, in its second case** (N+): the mirror
`truth ↦ 1 − truth` of the drift instance, with `T → +∞` and `T` bounded below.
Source: [[corr-li-shutdown-findings]] F11 (mirror); audit r3 adversarial B1
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem signedError_trichotomy_atTop_realized :
    (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 ∧
    Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2)) ∧
    (∀ i, (1 - driftTruth i) = 0 ∨ (1 - driftTruth i) = 1) ∧
    (∀ (η' M' : ℚ) (N₀ : ℕ), 0 < η' →
      Tendsto (prefixSum (runningSumRamp (fun i => (1 / 2 : ℝ) - (1 - driftTruth i)) η' M' N₀))
        atTop atTop →
      weightedAverage (runningSumRamp (fun i => (1 / 2 : ℝ) - (1 - driftTruth i)) η' M' N₀)
        (fun i => 1 - driftTruth i) ≈ₙ fun _ => (1 / 2 : ℝ)) ∧
    (∀ (η' M' : ℚ) (N₀ : ℕ), 0 < η' →
      Tendsto (prefixSum (runningSumRamp (fun i => (1 - driftTruth i) - (1 / 2 : ℝ)) η' M' N₀))
        atTop atTop →
      weightedAverage (runningSumRamp (fun i => (1 - driftTruth i) - (1 / 2 : ℝ)) η' M' N₀)
        (fun i => 1 - driftTruth i) ≈ₙ fun _ => (1 / 2 : ℝ)) ∧
    Tendsto (prefixSum (fun i => (1 / 2 : ℝ) - (1 - driftTruth i))) atTop atTop ∧
    BddBelow (Set.range (prefixSum (fun i => (1 / 2 : ℝ) - (1 - driftTruth i)))) := by
  refine ⟨by norm_num, by norm_num, tendsto_const_nhds, one_sub_driftTruth_boolean,
    fun η' M' N₀ hη' _ => driftMirror_upward_clause η' M' N₀ hη',
    fun η' M' N₀ hη' htend => driftMirror_downward_clause η' M' N₀ hη' htend, ?_, ?_⟩
  · rw [prefixSum_driftMirrorError, tendsto_atTop_atTop]
    intro b
    obtain ⟨K, hK⟩ := tendsto_atTop_atTop.mp tendsto_natSqrt_atTop (2 * b + 1)
    refine ⟨K, fun N hN => ?_⟩
    have h1 := hK N hN
    have h2 : (Nat.sqrt N : ℝ) - 1 ≤ driftExcess N := by exact_mod_cast (driftExcess_bounds N).1
    linarith
  · rw [prefixSum_driftMirrorError]
    refine ⟨-1 / 2, ?_⟩
    rintro _ ⟨N, rfl⟩
    have h : (Nat.sqrt N : ℝ) - 1 ≤ driftExcess N := by exact_mod_cast (driftExcess_bounds N).1
    have h0 : (0 : ℝ) ≤ Nat.sqrt N := Nat.cast_nonneg _
    show -1 / 2 ≤ (driftExcess N : ℝ) / 2
    linarith

end Cleanroom.Corrigibility.CorrLiShutdown
