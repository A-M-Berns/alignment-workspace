import Cleanroom.Found.LiAsympCalc.WeightedAverage
import Cleanroom.Found.LiAsympCalc.Spikes
import Mathlib.Analysis.PSeries

/-!
# `trust-merge` · Classwise: classwise Value from averaged Total Trust, defined and proved (T6)

**root-fa-039.** [[faithful-acceleration]] §5 line 161 concludes from the averaged above-threshold
inequality — the Corollary `Σ_{n≤N} g_n 𝔼^H_n(X_n) / Σ_{n≤N} g_n ≳ t − ε − δ` — that "by the §2
equivalence Total Trust ⟺ Value (applied to this class) `H` correspondingly **Values** `A`
classwise", without defining classwise Value or showing the equivalence commutes with the
gate-weighted average. This file defines it and answers the commutation question.

* `classwiseMean g y N := Σ_{n≤N} y_n / Σ_{n≤N} g_n` (FAF's zero-denominator guard): the
  gate-normalized mean of a per-menu quantity over the class of menus the gate indexes.
* `ClasswiseValue g S s := classwiseMean g (S − s) ≳ₙ 0`: averaged over the menus indexed by the
  gate, the followed strategy's value is at least the constant option's — "act on `A`'s advice as
  a standing policy over a class".
* **The identity averages exactly** (`classwiseValue_iff_averaged`): when the per-menu gap is the
  two-option identity `S_n − s = g_n (x_n − s)` (`def-lattice`'s `twoOptionComb_expect` /
  `twoOption_identity_above`, with `x_n = 𝔼^H_n(X_n)`, `g_n` the gate), classwise Value **is**
  the averaged above-threshold inequality `weightedAverage g (x − s) ≳ₙ 0`, both directions —
  the source's "yes, it commutes" for the exact identity. Once the identity is a hypothesis this
  is an unfolding (`classwiseMean g (g·x) = weightedAverage g x` by `simp only`), Kind L (audit
  r1, adversarial B2); the content of T6 is in the two slack lemmas and the counterexample below.
* **With reflection slack it commutes iff the slack is gate-negligible**
  (`classwiseValue_of_averaged_of_negligible`, `averaged_of_classwiseValue_of_negligible`): for
  `S_n − s = g_n (x_n − s) + e_n`, the two sides agree when `classwiseMean g e → 0`; the
  **counterexample** `classwise_slack_counterexample` (gate `1/(n+1)`, slack `−1/(n+1)`, both
  summing to the harmonic series) shows a *vanishing* slack of the gate's own order breaks the
  implication — the honest answer to the source's question: a per-day `→ 0` slack does **not**
  suffice; what averages is slack that is `o(gate mass)`.
* **N+ "consistent with one bad defer"** (`oneBadDefer_witness`): a gate and a price sequence whose
  per-menu gap is `−1` on every perfect square (infinitely often negative) yet whose classwise mean
  tends to `1/2 ≥ 0` — the honest limit the source states.

Real sequences in `li-asymp-calc`'s vocabulary throughout; the LUV instance (classwise hedged
Value on `twoOptionComb` menus) is `ClasswiseLUV.lean`. No inductor is constructed here.
-/

namespace Cleanroom.Trust.TrustMerge

open LogicalInduction Filter Topology Finset
open Cleanroom.Found.LiAsympCalc

noncomputable section

/-- **The gate-normalized classwise mean** `Σ_{n≤N} y_n / Σ_{n≤N} g_n` (FAF's guard: `0` while the
gate mass is `0`). With `y_n` the per-menu Value gap, this is "averaged over the menus indexed by
the class".
Source: root-fa-039 (the missing definition); [[faithful-acceleration]] §5 l. 161
Kind: D
Fidelity: exact (the guard as FAF's `weightedAverage`)
Hyps: n/a -/
def classwiseMean (g y : ℕ → ℝ) (N : ℕ) : ℝ :=
  if prefixSum g N = 0 then 0 else prefixSum y N / prefixSum g N

/-- **Classwise Value** of a per-menu strategy value `S` against the constant `s`, over the class
the gate `g` indexes: `classwiseMean g (S − s) ≳ₙ 0`.
Source: root-fa-039; [[faithful-acceleration]] §5 l. 161 ("averaged over the menus indexed by the
class, `H` weakly prefers to let `A` pick rather than commit to a fixed option");
[[pointwise-tower-and-faithful-acceleration]] §4.4
Kind: D
Fidelity: variant: no divergence condition in the definition (the mandate's object has
`Σ g = ∞` inside); divergence is carried by every theorem about it, and at the null gate the
predicate is trivially true (`classwiseValue_null_gate`; audit r2 adversarial N4)
Hyps: n/a -/
def ClasswiseValue (g S : ℕ → ℝ) (s : ℝ) : Prop :=
  classwiseMean g (fun n => S n - s) ≳ₙ (fun _ => (0 : ℝ))

/-- **At the null gate classwise Value is trivially true** for every `S` and `s`: the guarded
mean is `0`. The definition carries no divergence condition — FAF's pattern for
`weightedAverage` — and every theorem about it takes `hdiv`; this is the junk value, disclosed
at the definition (audit r2 adversarial N4, probe ported).
Source: audit r2 adversarial N4 (probe `ClasswiseNullGate.lean`)
Kind: T (a junk-value disclosure)
Fidelity: n/a
Hyps: n/a -/
theorem classwiseValue_null_gate (S : ℕ → ℝ) (s : ℝ) : ClasswiseValue (fun _ => 0) S s := by
  unfold ClasswiseValue
  have h : classwiseMean (fun _ => (0 : ℝ)) (fun n => S n - s) = fun _ => 0 := by
    funext N
    simp [classwiseMean, prefixSum]
  rw [h]
  intro ε hε
  filter_upwards with N
  simp
  exact hε.le

/-- The classwise mean of a gated quantity is FAF's weighted average: `classwiseMean g (g·x) =
weightedAverage g x`, definitionally (same guard).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem classwiseMean_gate_mul (g x : ℕ → ℝ) :
    classwiseMean g (fun n => g n * x n) = weightedAverage g x := by
  funext N
  simp only [classwiseMean, weightedAverage]

/-- **T6 (headline). The two-option identity averages exactly:** when the per-menu gap is
`S_n − s = g_n (x_n − s)` (the hedged two-option identity, `def-lattice`'s `twoOptionComb_expect`
with `x_n = 𝔼^H_n(X_n)` and the gate `g_n` the realized weight), classwise Value **is** the
averaged above-threshold inequality `weightedAverage g (x − s) ≳ₙ 0`, in both directions. The
source's Corollary (input (b): `fa-forcing-trader`'s) therefore yields classwise Value for the
gated two-option family by linearity alone — and conversely. **Kind L**: with the identity as a
hypothesis the two sides are the same expression (`classwiseMean_gate_mul` is `simp only` of the
two definitions); the statement is worth having, the proof is an unfolding (audit r1,
adversarial B2). T6's content is `classwiseValue_of_averaged_of_negligible` /
`averaged_of_classwiseValue_of_negligible` and `classwise_slack_counterexample`.
Source: root-fa-039 ("prove averaged TT ⇒ classwise Value by linearity of the witness identity —
if the per-menu equivalence is an identity of quantities it should average"); [[faithful-
acceleration]] §5 l. 161
Kind: L
Fidelity: exact
Hyps: (a) none (the identity `hS` is the two-option identity, supplied by the LUV instance) -/
theorem classwiseValue_iff_averaged (g x S : ℕ → ℝ) (s : ℝ)
    (hS : ∀ n, S n - s = g n * (x n - s)) :
    ClasswiseValue g S s ↔ weightedAverage g (fun n => x n - s) ≳ₙ (fun _ => (0 : ℝ)) := by
  unfold ClasswiseValue
  have : (fun n => S n - s) = fun n => g n * (x n - s) := funext hS
  rw [this, classwiseMean_gate_mul]

/-- The classwise mean is additive where the gate mass is nonzero.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem classwiseMean_add (g y e : ℕ → ℝ) {N : ℕ} (h : prefixSum g N ≠ 0) :
    classwiseMean g (fun n => y n + e n) N = classwiseMean g y N + classwiseMean g e N := by
  simp only [classwiseMean, if_neg h, prefixSum_add, add_div]

/-- **Forward direction with slack:** if `S_n − s = g_n (x_n − s) + e_n` and the slack is
gate-negligible (`classwiseMean g e → 0`), the averaged inequality gives classwise Value. The
commutation the source asks for, with the hypothesis it needs made explicit.
Source: root-fa-039 ("if it is an implication with a tolerance, the averaged version needs
care"); mandate T6
Kind: P
Fidelity: exact
Hyps: (a) none (`hneg` is the negligibility condition; `classwise_slack_counterexample` shows it
is not implied by `e → 0`) -/
theorem classwiseValue_of_averaged_of_negligible (g x S e : ℕ → ℝ) (s : ℝ)
    (hS : ∀ n, S n - s = g n * (x n - s) + e n)
    (hdiv : Tendsto (prefixSum g) atTop atTop)
    (hneg : Tendsto (classwiseMean g e) atTop (𝓝 0))
    (h : weightedAverage g (fun n => x n - s) ≳ₙ (fun _ => (0 : ℝ))) :
    ClasswiseValue g S s := by
  unfold ClasswiseValue
  have hfun : (fun n => S n - s) = fun n => g n * (x n - s) + e n := funext hS
  rw [hfun]
  intro ε hε
  have hev := eventually_prefixSum_pos hdiv
  have hε2 : (0 : ℝ) < ε / 2 := by positivity
  have hneg' := (Metric.tendsto_nhds.1 hneg) (ε / 2) hε2
  filter_upwards [hev, h (ε / 2) hε2, hneg'] with N hN hx he
  rw [classwiseMean_add g _ _ hN.ne', classwiseMean_gate_mul]
  rw [Real.dist_eq, sub_zero] at he
  have := (abs_lt.1 he).1
  linarith

/-- **Converse with slack:** classwise Value plus gate-negligible slack gives the averaged
inequality.
Source: root-fa-039 ("prove the converse too (same identity)")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem averaged_of_classwiseValue_of_negligible (g x S e : ℕ → ℝ) (s : ℝ)
    (hS : ∀ n, S n - s = g n * (x n - s) + e n)
    (hdiv : Tendsto (prefixSum g) atTop atTop)
    (hneg : Tendsto (classwiseMean g e) atTop (𝓝 0))
    (h : ClasswiseValue g S s) :
    weightedAverage g (fun n => x n - s) ≳ₙ (fun _ => (0 : ℝ)) := by
  unfold ClasswiseValue at h
  have hfun : (fun n => S n - s) = fun n => g n * (x n - s) + e n := funext hS
  rw [hfun] at h
  intro ε hε
  have hev := eventually_prefixSum_pos hdiv
  have hε2 : (0 : ℝ) < ε / 2 := by positivity
  have hneg' := (Metric.tendsto_nhds.1 hneg) (ε / 2) hε2
  filter_upwards [hev, h (ε / 2) hε2, hneg'] with N hN hx he
  rw [classwiseMean_add g _ _ hN.ne', classwiseMean_gate_mul] at hx
  rw [Real.dist_eq, sub_zero] at he
  have := (abs_lt.1 he).2
  linarith

/-! ## N+: the commutation fails for a vanishing slack of the gate's order -/

/-- **N+ (the source's commutation question, answered negatively for vanishing slack):** gate
`g_n = 1/(n+1)` (in `[0,1]`, divergent — the harmonic series) and slack `e_n = −1/(n+1)` (→ 0):
the averaged inequality holds trivially (`x ≡ s`), yet classwise Value **fails** — the classwise
mean of the slack is `−1` on every day. A per-day vanishing reflection slack does not average
away against a thin gate; the equivalence commutes with the gate-weighted average only for
slack that is `o(gate mass)` (`hneg` of the theorems above).
Source: root-fa-039 ("does the equivalence commute with the gate-weighted average?"); mandate T6
Kind: N+
Fidelity: exact
Hyps: n/a -/
theorem classwise_slack_counterexample :
    ∃ (g e : ℕ → ℝ) (s : ℝ),
      (∀ n, 0 ≤ g n ∧ g n ≤ 1) ∧ Tendsto (prefixSum g) atTop atTop ∧
      Tendsto e atTop (𝓝 0) ∧
      (weightedAverage g (fun n => s - s) ≳ₙ (fun _ => (0 : ℝ))) ∧
      ¬ ClasswiseValue g (fun n => s + g n * (s - s) + e n) s := by
  refine ⟨fun n => 1 / ((n : ℝ) + 1), fun n => -(1 / ((n : ℝ) + 1)), 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    have h0 : (0 : ℝ) ≤ n := n.cast_nonneg
    constructor
    · positivity
    · rw [div_le_one (by positivity)]
      linarith
  · have h := Real.tendsto_sum_range_one_div_nat_succ_atTop
    have heq : prefixSum (fun n => 1 / ((n : ℝ) + 1)) =
        fun N => ∑ i ∈ range (N + 1), 1 / ((i : ℝ) + 1) := by
      funext N
      simp [prefixSum]
    rw [heq]
    exact h.comp (tendsto_add_atTop_nat 1)
  · have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using this.neg
  · have hz : weightedAverage (fun n => 1 / ((n : ℝ) + 1)) (fun _ => (0 : ℝ) - 0) =
        fun _ => 0 := by
      funext N
      simp [weightedAverage, prefixSum]
    rw [hz]
    intro ε hε
    filter_upwards with N
    simp
    linarith
  · intro h
    have hev := h (1 / 2) (by norm_num)
    have hpos : ∀ N, prefixSum (fun n => 1 / ((n : ℝ) + 1)) N ≠ 0 := by
      intro N
      apply ne_of_gt
      unfold prefixSum
      apply Finset.sum_pos (fun i _ => by positivity) ⟨0, by simp⟩
    have hval : ∀ N, classwiseMean (fun n => 1 / ((n : ℝ) + 1))
        (fun n => (0 : ℝ) + 1 / ((n : ℝ) + 1) * (0 - 0) + -(1 / ((n : ℝ) + 1)) - 0) N = -1 := by
      intro N
      simp only [classwiseMean, if_neg (hpos N), sub_zero, mul_zero, add_zero, zero_add]
      rw [show prefixSum (fun n => -(1 / ((n : ℝ) + 1))) N =
          -prefixSum (fun n => 1 / ((n : ℝ) + 1)) N by
        simp [prefixSum, Finset.sum_neg_distrib]]
      rw [neg_div, div_self (hpos N)]
    obtain ⟨N, hN⟩ := hev.exists
    rw [hval N] at hN
    norm_num at hN

/-! ## N+: consistent with one bad defer -/

/-- **N+ ("consistent with one bad defer"):** with the trivial gate `g ≡ 1` and per-menu gap
`x_n − s = −1` on every perfect square and `+1` elsewhere, the gap is negative infinitely often
yet the classwise (Cesàro) mean is `≥ 0` from day `8` on (at most `√N + 1` squares below `N`), so
classwise Value holds. The averaged guarantee is silent about any single menu — the limit
[[faithful-acceleration]] §5 states, and T7's "one big lie" at the level of this file.
Source: root-fa-039; [[faithful-acceleration]] §5 ("consistent with one bad defer"); trust-lab-015
Kind: N+
Fidelity: exact
Hyps: n/a -/
theorem oneBadDefer_witness :
    ∃ (x : ℕ → ℝ) (s : ℝ),
      (∀ N, ∃ n, N ≤ n ∧ x n - s < 0) ∧
      ClasswiseValue (fun _ => 1) (fun n => s + 1 * (x n - s)) s := by
  refine ⟨fun n => 1 - 2 * squareSpikes n, 0, ?_, ?_⟩
  · intro N
    refine ⟨N * N, Nat.le_mul_self N, ?_⟩
    have hsq : squareSpikes (N * N) = 1 := by
      unfold squareSpikes
      exact if_pos (⟨N, rfl⟩ : IsSquare (N * N))
    simp only [hsq]
    norm_num
  · unfold ClasswiseValue
    have hfun : (fun n => (0 : ℝ) + 1 * (1 - 2 * squareSpikes n - 0) - 0) =
        fun n => (1 : ℝ) * (1 - 2 * squareSpikes n) := by
      funext n; ring
    rw [hfun, classwiseMean_gate_mul]
    intro ε hε
    filter_upwards [eventually_ge_atTop 8] with N hN
    have hden : prefixSum (fun _ : ℕ => (1 : ℝ)) N = (N : ℝ) + 1 := by
      simp [prefixSum]
    have hnum : prefixSum (fun i => (1 : ℝ) * (1 - 2 * squareSpikes i)) N =
        ((N : ℝ) + 1) - 2 * ∑ i ∈ range (N + 1), squareSpikes i := by
      simp only [prefixSum, one_mul, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, Finset.mul_sum]
      push_cast
      ring
    have hsum := sum_squareSpikes_le (N + 1)
    have hs3 : 3 ≤ Nat.sqrt (N + 1) := by
      rw [Nat.le_sqrt]
      omega
    have hsq : Nat.sqrt (N + 1) * Nat.sqrt (N + 1) ≤ N + 1 := Nat.sqrt_le (N + 1)
    have hineq : (2 : ℝ) * (((Nat.sqrt (N + 1) : ℕ) : ℝ) + 1) ≤ (N : ℝ) + 1 := by
      have h3 : (3 : ℝ) ≤ ((Nat.sqrt (N + 1) : ℕ) : ℝ) := by exact_mod_cast hs3
      have hsq' : ((Nat.sqrt (N + 1) : ℕ) : ℝ) * ((Nat.sqrt (N + 1) : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by
        exact_mod_cast hsq
      nlinarith
    have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hwa : weightedAverage (fun _ => (1 : ℝ)) (fun n => 1 - 2 * squareSpikes n) N =
        (((N : ℝ) + 1) - 2 * ∑ i ∈ range (N + 1), squareSpikes i) / ((N : ℝ) + 1) := by
      rw [weightedAverage_eq_div (by rw [hden]; exact hNpos.ne'), hden, hnum]
    have hnonneg : 0 ≤ (((N : ℝ) + 1) - 2 * ∑ i ∈ range (N + 1), squareSpikes i) / ((N : ℝ) + 1) :=
      div_nonneg (by linarith) hNpos.le
    show (0 : ℝ) ≤ _ + ε
    rw [hwa]
    linarith

end

end Cleanroom.Trust.TrustMerge
