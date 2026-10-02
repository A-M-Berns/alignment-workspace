import Cleanroom.Fa.FaTheoremA.Defs
import Cleanroom.Found.LiAsympCalc.WeightedAverage
import Cleanroom.Found.LiAsympCalc.Compactness

/-!
# `fa-theorem-a` · Analysis: the pure-analysis steps of the gate argument

The real-sequence lemmas that Theorem A's proof ([[faithful-acceleration-result]] §4.2) and
Lemma P's ([[route-negative-introspective]] §7) use between the two FAF endpoints: a gate that
is `1` infinitely often has divergent prefix sums (the "divergent" step); the weighted average
over a support where `x ≥ a` is `≥ a` (the "no false positives" step of Half 1's corollary); the
realized sequence `Y_n = 𝔼^H_{f n}(X)` inherits the limit of `𝔼^H_n(X)` because `f n → ∞`; and
two sequences with a common limit dominate each other (the step from Lemma P to the `Dominates`
form). No inductor appears in this file; everything is over FAF's `prefixSum`/`weightedAverage`
and `li-asymp-calc`'s `Dominates`.
-/

namespace Cleanroom.Fa.FaTheoremA

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Filter Topology

/-! ## A. Divergence of a gate that fires infinitely often -/

/-- Prefix sums of a nonnegative sequence are monotone in the day.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma prefixSum_mono {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) : Monotone (prefixSum w) := by
  intro m n hmn
  unfold prefixSum
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hmn))
    (fun i _ _ => hw i)

/-- **The divergence step.** A nonnegative weighting that is `≥ 1` on infinitely many days has
divergent (inclusive) prefix sums — the "`u` is divergent, since infinitely many days carry
weight `1`" step of Theorem A's proof. `li-asymp-calc`'s `tendsto_prefixSum_one` is the uniform
special case.
Source: [[faithful-acceleration-result]] §4.2 ("divergent, since … infinitely many days carry weight `1`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem tendsto_prefixSum_atTop_of_frequently_one {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hfreq : ∃ᶠ n in atTop, 1 ≤ w n) : Tendsto (prefixSum w) atTop atTop := by
  refine tendsto_atTop_atTop_of_monotone (prefixSum_mono hw) ?_
  have key : ∀ k : ℕ, ∃ a, (k : ℝ) ≤ prefixSum w a := by
    intro k
    induction k with
    | zero => exact ⟨0, by simpa using prefixSum_nonneg hw 0⟩
    | succ k ih =>
      obtain ⟨a, ha⟩ := ih
      obtain ⟨m, hm, hwm⟩ := (frequently_atTop.1 hfreq) (a + 1)
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      refine ⟨m' + 1, ?_⟩
      rw [prefixSum_succ]
      have hmono : prefixSum w a ≤ prefixSum w m' := prefixSum_mono hw (by omega)
      push_cast
      linarith
  intro b
  obtain ⟨a, ha⟩ := key ⌈b⌉₊
  exact ⟨a, (Nat.le_ceil b).trans ha⟩

/-! ## B. Weighted averages over a one-sided support -/

/-- If `x ≥ a` wherever the weight is positive, the weighted average is `≥ a` (positive mass).
Source: [[route-recurring-ccee]] §4 ("the ramp has no false positives, so `u_i > 0 ⇒ a_i > t`, whence `ā_n ≥ t` for every `n`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
lemma le_weightedAverage_of_support {w x : ℕ → ℝ} {a : ℝ} {n : ℕ} (hw : ∀ i, 0 ≤ w i)
    (hsupp : ∀ i, 0 < w i → a ≤ x i) (hden : 0 < prefixSum w n) :
    a ≤ weightedAverage w x n := by
  rw [weightedAverage_eq_div hden.ne', le_div_iff₀ hden]
  unfold prefixSum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rcases (hw i).lt_or_eq with h | h
  · calc a * w i = w i * a := mul_comm _ _
      _ ≤ w i * x i := mul_le_mul_of_nonneg_left (hsupp i h) (hw i)
  · rw [← h]; simp

/-- If `x ≤ b` wherever the weight is positive, the weighted average is `≤ b` (positive mass).
Source: [[route-recurring-ccee]] §4 (the dual gate)
Kind: L
Fidelity: exact
Hyps: (a) none -/
lemma weightedAverage_le_of_support {w x : ℕ → ℝ} {b : ℝ} {n : ℕ} (hw : ∀ i, 0 ≤ w i)
    (hsupp : ∀ i, 0 < w i → x i ≤ b) (hden : 0 < prefixSum w n) :
    weightedAverage w x n ≤ b := by
  rw [weightedAverage_eq_div hden.ne', div_le_iff₀ hden]
  unfold prefixSum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rcases (hw i).lt_or_eq with h | h
  · calc w i * x i ≤ w i * b := mul_le_mul_of_nonneg_left (hsupp i h) (hw i)
      _ = b * w i := mul_comm _ _
  · rw [← h]; simp

/-! ## C. The realized sequence inherits the limit -/

/-- A deferral function tends to infinity (`n < f n`).
Source: none: infrastructure (FAF `DeferralFunction.lt`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma deferral_tendsto_atTop (f : DeferralFunction) : Tendsto f.f atTop atTop :=
  tendsto_atTop_mono (fun n => (f.lt n).le) tendsto_id

/-- **The subsequence step.** If `𝔼^H_n(X) → L` then the realized `Y_n = 𝔼^H_{f n}(X) → L`:
"the determined values `Y_n = 𝔼^H_{f(n)}(X) → p_∞` as a subsequence of a convergent sequence"
(for an arbitrary deferral function, not necessarily monotone — composition with `f n → ∞`).
Source: [[faithful-acceleration-result]] §4.2
Kind: L
Fidelity: stronger: `f` need not be increasing
Hyps: (a) none -/
theorem tendsto_realized_of_tendsto {H : History} (f : DeferralFunction) (X : LUV) {L : ℝ}
    (h : Tendsto (X.expectSeq H) atTop (𝓝 L)) :
    Tendsto (realized H f (fun _ => X)) atTop (𝓝 L) :=
  h.comp (deferral_tendsto_atTop f)

/-- The varying-family form: if `𝔼^H_{f n}(X n)` is given to converge, nothing is needed (stated
for symmetry with `tendsto_realized_of_tendsto`; Theorem A's varying extension T11 takes this as
an antecedent, not a conclusion).
Source: [[open-problems]] item 8 (vq-wiki-032)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem tendsto_realized_iff {H : History} (f : DeferralFunction) (X : ℕ → LUV) {L : ℝ} :
    Tendsto (realized H f X) atTop (𝓝 L) ↔
      Tendsto (fun n => (X n).expect H (f.f n)) atTop (𝓝 L) := Iff.rfl

/-! ## D. From a common limit to dominance and asymptotic equality -/

/-- **The dominance step.** Two sequences with the same limit dominate each other: for every
`c > 0`, eventually `a n − c < e n`.
Source: [[fa-positive-results-corrected-v3]] §5 (`Dominates`); [[faithful-acceleration-result]] §4.2 (the conclusion's form)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem dominates_of_tendsto {e a : ℕ → ℝ} {L : ℝ} (he : Tendsto e atTop (𝓝 L))
    (ha : Tendsto a atTop (𝓝 L)) : Dominates e a := by
  intro c hc
  have h1 := (Metric.tendsto_nhds.1 he) (c / 2) (by positivity)
  have h2 := (Metric.tendsto_nhds.1 ha) (c / 2) (by positivity)
  filter_upwards [h1, h2] with n hn1 hn2
  rw [Real.dist_eq, abs_sub_lt_iff] at hn1 hn2
  linarith [hn1.1, hn1.2, hn2.1, hn2.2]

/-- Two sequences with the same limit are asymptotically equal (`≈ₙ`).
Source: none: infrastructure (FAF `AsympEq`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem asympEq_of_tendsto {a e : ℕ → ℝ} {L : ℝ} (ha : Tendsto a atTop (𝓝 L))
    (he : Tendsto e atTop (𝓝 L)) : AsympEq a e := by
  unfold AsympEq
  simpa using ha.sub he

/-- Dominance both ways is asymptotic equality.
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem asympEq_of_dominates {a e : ℕ → ℝ} (h1 : Dominates e a) (h2 : Dominates a e) :
    AsympEq a e := by
  unfold AsympEq
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h1 ε hε, h2 ε hε] with n hn1 hn2
  rw [Real.dist_eq, sub_zero, abs_sub_lt_iff]
  constructor <;> linarith

end Cleanroom.Fa.FaTheoremA
