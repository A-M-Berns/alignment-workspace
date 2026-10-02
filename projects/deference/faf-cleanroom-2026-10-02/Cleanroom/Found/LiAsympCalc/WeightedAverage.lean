import Cleanroom.Found.LiAsympCalc.Defs
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries

/-!
# A. Weighted-average calculus over FAF's `weightedAverage`, and Kronecker's lemma

Target A of [[li-asymp-calc-mandate]]. Everything is stated over FAF's total `weightedAverage`
(value `0` at zero mass) and inclusive `prefixSum`; the zero-mass branch is discharged
eventually from divergence (`eventually_prefixSum_pos`), never assumed away.

* A1: `WeightedApprox` is reflexive, symmetric, transitive *for one weighting*, additive and
  stable under constant scaling. Only symmetry-free facts need the divergence hypothesis; none
  needs nonnegativity beyond what divergence supplies, so hypotheses are stated as narrowly as
  the proofs use them (the mandate's `hw, hdiv` package is a sufficient condition).
  Transitivity across two different weightings is false and not stated.
* A2: the **universal donor rule** `weightedAverage_tendsto_zero` — a sequence tending to `0` has
  weighted averages tending to `0` under every nonnegative divergent weighting, with **no
  boundedness hypothesis** (the mandate's finding about [[route-sparse-schedule]] §7 Lemma 2);
  its `l`-valued form, the finite-prefix wash-out, the `EF` form from `DivergentWeighting`, the
  `weightedBias` spelling, and the exclusive-Cesàro bridge to Mathlib's `Filter.Tendsto.cesaro`.
* A3: **Kronecker's lemma** in the conditional form (partial sums of `x n / b n` converge; no
  `Summable`), by an Abel-type identity and the donor rule, plus the inclusive-`prefixSum` variant
  and the conditionally-but-not-absolutely summable witness `(-1)^n / (n+1)`.
-/

namespace Cleanroom.Found.LiAsympCalc

open LogicalInduction Filter Topology Finset

/-! ### Basic facts about FAF's prefix sums -/

/-- Divergent prefix sums are eventually positive (FAF's idiom
`DivergentWeighting.eventually_prefixSum_pos`, for a bare real weighting).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma eventually_prefixSum_pos {w : ℕ → ℝ} (hdiv : Tendsto (prefixSum w) atTop atTop) :
    ∀ᶠ n in atTop, 0 < prefixSum w n :=
  hdiv.eventually (eventually_gt_atTop 0)

/-- Prefix sums of a nonnegative sequence are nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma prefixSum_nonneg {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (n : ℕ) : 0 ≤ prefixSum w n :=
  Finset.sum_nonneg (fun i _ => hw i)

/-! ### A1. The calculus of `≈_{w̄}` -/

/-- `x ≈_{w̄} x`, for every weighting (the averaged difference is identically `0`).
Source: [[theorem-ss-streamlined]] §1; `StreamlinedSS.lean:137`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem WeightedApprox.refl (w x : ℕ → ℝ) : WeightedApprox w x x := by
  have h : weightedAverage w (fun i => x i - x i) = fun _ => 0 := by
    funext n
    simp [weightedAverage, prefixSum]
  unfold WeightedApprox
  rw [h]
  exact tendsto_const_nhds

/-- `x ≈_{w̄} y → y ≈_{w̄} x`, for every weighting (negation passes through FAF's average,
zero-mass branch included).
Source: [[theorem-ss-streamlined]] §1; `StreamlinedSS.lean:137`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem WeightedApprox.symm {w x y : ℕ → ℝ} (h : WeightedApprox w x y) :
    WeightedApprox w y x := by
  unfold WeightedApprox at *
  have hneg : weightedAverage w (fun i => y i - x i) =
      fun n => -weightedAverage w (fun i => x i - y i) n := by
    funext n
    rw [← weightedAverage_neg]
    congr 1
    funext i
    ring
  rw [hneg]
  simpa using h.neg

/-- Transitivity of `≈_{w̄}` **for one weighting** `w` with divergent mass. Across two different
weightings the relation is not transitive (not stated).
Source: [[theorem-ss-streamlined]] §1; `StreamlinedSS.lean:137`
Kind: L
Fidelity: exact
Hyps: (a) divergence only (nonnegativity is not needed) -/
theorem WeightedApprox.trans {w x y z : ℕ → ℝ} (hdiv : Tendsto (prefixSum w) atTop atTop)
    (hxy : WeightedApprox w x y) (hyz : WeightedApprox w y z) : WeightedApprox w x z := by
  unfold WeightedApprox at *
  have hev : (fun n => weightedAverage w (fun i => x i - y i) n +
      weightedAverage w (fun i => y i - z i) n) =ᶠ[atTop]
      weightedAverage w (fun i => x i - z i) := by
    filter_upwards [eventually_prefixSum_pos hdiv] with n hn
    rw [← weightedAverage_add w _ _ hn.ne']
    congr 1
    funext i
    ring
  have hsum : Tendsto (fun n => weightedAverage w (fun i => x i - y i) n +
      weightedAverage w (fun i => y i - z i) n) atTop (𝓝 0) := by
    simpa using hxy.add hyz
  exact hsum.congr' hev

/-- Additivity of `≈_{w̄}` for one divergent weighting.
Source: [[theorem-ss-streamlined]] §1; `StreamlinedSS.lean:137`
Kind: L
Fidelity: exact
Hyps: (a) divergence only -/
theorem WeightedApprox.add {w x y x' y' : ℕ → ℝ} (hdiv : Tendsto (prefixSum w) atTop atTop)
    (h₁ : WeightedApprox w x y) (h₂ : WeightedApprox w x' y') :
    WeightedApprox w (fun i => x i + x' i) (fun i => y i + y' i) := by
  unfold WeightedApprox at *
  have hev : (fun n => weightedAverage w (fun i => x i - y i) n +
      weightedAverage w (fun i => x' i - y' i) n) =ᶠ[atTop]
      weightedAverage w (fun i => (x i + x' i) - (y i + y' i)) := by
    filter_upwards [eventually_prefixSum_pos hdiv] with n hn
    rw [← weightedAverage_add w _ _ hn.ne']
    congr 1
    funext i
    ring
  have hsum : Tendsto (fun n => weightedAverage w (fun i => x i - y i) n +
      weightedAverage w (fun i => x' i - y' i) n) atTop (𝓝 0) := by
    simpa using h₁.add h₂
  exact hsum.congr' hev

/-- Constant scaling preserves `≈_{w̄}`, for every weighting.
Source: [[theorem-ss-streamlined]] §1; `StreamlinedSS.lean:137`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem WeightedApprox.const_mul {w x y : ℕ → ℝ} (c : ℝ) (h : WeightedApprox w x y) :
    WeightedApprox w (fun i => c * x i) (fun i => c * y i) := by
  unfold WeightedApprox at *
  have hc : weightedAverage w (fun i => c * x i - c * y i) =
      fun n => c * weightedAverage w (fun i => x i - y i) n := by
    funext n
    rw [← weightedAverage_const_mul]
    congr 1
    funext i
    ring
  rw [hc]
  simpa using h.const_mul c

/-! ### A2. The universal donor rule -/

/-- Finite-prefix plus tail bound: if `|r i| ≤ η` from day `N` on, the weighted average is within
`η` of a term that the finite prefix `∑ i < N, w i * |r i|` controls, divided by the mass.
Source: none: infrastructure (`StreamlinedSS.lean:166–226`)
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma abs_weightedAverage_le_of_tail {w r : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) {N : ℕ} {η : ℝ}
    (hη : ∀ i, N ≤ i → |r i| ≤ η) {n : ℕ} (hn : 0 < prefixSum w n) :
    |weightedAverage w r n| ≤ (∑ i ∈ range N, w i * |r i|) / prefixSum w n + η := by
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hη N le_rfl)
  have key : |prefixSum (fun i => w i * r i) n| ≤
      (∑ i ∈ range N, w i * |r i|) + η * prefixSum w n := by
    calc |prefixSum (fun i => w i * r i) n|
        ≤ ∑ i ∈ range (n + 1), |w i * r i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ range (n + 1), w i * |r i| := by
          apply Finset.sum_congr rfl
          intro i _
          rw [abs_mul, abs_of_nonneg (hw i)]
      _ ≤ ∑ i ∈ range (n + 1), ((if i < N then w i * |r i| else 0) + η * w i) := by
          apply Finset.sum_le_sum
          intro i _
          split_ifs with hi
          · have := mul_nonneg hη0 (hw i)
            linarith
          · have := hη i (not_lt.1 hi)
            calc w i * |r i| ≤ w i * η := mul_le_mul_of_nonneg_left this (hw i)
              _ = 0 + η * w i := by ring
      _ = (∑ i ∈ range (n + 1), if i < N then w i * |r i| else 0) + η * prefixSum w n := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          rfl
      _ ≤ (∑ i ∈ range N, w i * |r i|) + η * prefixSum w n := by
          gcongr
          rw [← Finset.sum_filter]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi
            simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
            exact hi.2
          · intro i _ _
            exact mul_nonneg (hw i) (abs_nonneg _)
  have hd := hn.ne'
  rw [weightedAverage_eq_div hd, abs_div, abs_of_pos hn]
  calc |prefixSum (fun i => w i * r i) n| / prefixSum w n
      ≤ ((∑ i ∈ range N, w i * |r i|) + η * prefixSum w n) / prefixSum w n :=
        div_le_div_of_nonneg_right key hn.le
    _ = (∑ i ∈ range N, w i * |r i|) / prefixSum w n + η := by
        field_simp

/-- At the zero weighting every pair is `WeightedApprox`, because FAF's `weightedAverage` is
`0` at zero mass. Recorded so that no dependent states a `WeightedApprox` conclusion without a
divergence hypothesis beside it (see the convention list in `Defs`).
Source: none: infrastructure (audit round 1, adversarial probe 1)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem weightedApprox_zero_total (x y : ℕ → ℝ) : WeightedApprox (fun _ => 0) x y := by
  unfold WeightedApprox
  have h : weightedAverage (fun _ : ℕ => (0 : ℝ)) (fun i => x i - y i) = fun _ => 0 := by
    funext n
    simp [weightedAverage, prefixSum]
  rw [h]
  exact tendsto_const_nhds

/-- **Universal donor rule** (A2): a sequence tending to `0` has weighted averages tending to
`0` under every nonnegative weighting with divergent mass — no boundedness hypothesis, exactly
as the sources state it ([[route-sparse-schedule]] §7 Lemma 2 drops the bound and says why;
`StreamlinedSS.lean` `wavg_tendsto_zero` takes none).
Source: [[theorem-ss-streamlined]] §1; `StreamlinedSS.lean:166–226`; [[route-sparse-schedule]] §7 Lemma 2; anson-052
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem weightedAverage_tendsto_zero {w r : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (prefixSum w) atTop atTop) (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (weightedAverage w r) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hr ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hr (ε / 2) (by linarith)
  have hN' : ∀ i, N ≤ i → |r i| ≤ ε / 2 := fun i hi => by
    have := hN i hi
    rw [Real.dist_eq, sub_zero] at this
    exact this.le
  have hlim : Tendsto (fun n => (∑ i ∈ range N, w i * |r i|) / prefixSum w n) atTop (𝓝 0) :=
    hdiv.const_div_atTop _
  obtain ⟨M, hM⟩ := eventually_atTop.1
    ((eventually_prefixSum_pos hdiv).and (hlim.eventually (gt_mem_nhds (by linarith :
      (0 : ℝ) < ε / 2))))
  refine ⟨M, fun n hn => ?_⟩
  obtain ⟨hpos, hsmall⟩ := hM n hn
  rw [Real.dist_eq, sub_zero]
  calc |weightedAverage w r n|
      ≤ (∑ i ∈ range N, w i * |r i|) / prefixSum w n + ε / 2 :=
        abs_weightedAverage_le_of_tail hw hN' hpos
    _ < ε := by linarith

/-- The donor rule at a general limit: `r → l` gives `weightedAverage w r → l` (regularity of
the weighted-mean summation method).
Source: anson-052 (`dose-response.md` §4)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem weightedAverage_tendsto {w r : ℕ → ℝ} {l : ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (prefixSum w) atTop atTop) (hr : Tendsto r atTop (𝓝 l)) :
    Tendsto (weightedAverage w r) atTop (𝓝 l) := by
  have h0 : Tendsto (weightedAverage w (fun i => r i - l)) atTop (𝓝 0) :=
    weightedAverage_tendsto_zero hw hdiv (by simpa using hr.sub_const l)
  have hev : (fun n => weightedAverage w (fun i => r i - l) n + l) =ᶠ[atTop]
      weightedAverage w r := by
    filter_upwards [eventually_prefixSum_pos hdiv] with n hn
    rw [weightedAverage_sub w r (fun _ => l) hn.ne', weightedAverage_const w l hn.ne']
    ring
  have := h0.add_const l
  rw [zero_add] at this
  exact this.congr' hev

/-- A2 in the `WeightedApprox` spelling: pointwise `x - y → 0` donates `x ≈_{w̄} y` to every
nonnegative divergent weighting.
Source: [[theorem-ss-streamlined]] §1; [[route-sparse-schedule]] §7 Lemma 2
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem weightedApprox_of_tendsto_zero {w x y : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (prefixSum w) atTop atTop)
    (h : Tendsto (fun i => x i - y i) atTop (𝓝 0)) : WeightedApprox w x y :=
  weightedAverage_tendsto_zero hw hdiv h

/-- **Finite-prefix wash-out** (A2″): a sequence vanishing from day `N` on averages to `0` under
every nonnegative divergent weighting. No boundedness hypothesis: a finite prefix is bounded.
Source: anson-052 (`dose-response.md` §4)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem weightedAverage_tendsto_zero_of_eventually_zero {w r : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (prefixSum w) atTop atTop) {N : ℕ} (hr : ∀ n, N ≤ n → r n = 0) :
    Tendsto (weightedAverage w r) atTop (𝓝 0) :=
  weightedAverage_tendsto_zero hw hdiv
    (tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => (hr n hn).symm⟩))

/-- A2′: the `EF` form. A `DivergentWeighting W P` (FAF, `Properties/Calibration.lean`) realises
`w := fun i => (W i).denote P`, so pointwise `m - τ → 0` gives `m ≈_{w̄} τ`.
Source: [[theorem-ss-streamlined]] §1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem DivergentWeighting.weightedApprox {W : ℕ → EF} {P : History}
    (hW : DivergentWeighting W P) {m τ : ℕ → ℝ}
    (h : Tendsto (fun i => m i - τ i) atTop (𝓝 0)) :
    WeightedApprox (fun i => (W i).denote P) m τ :=
  weightedAverage_tendsto_zero (fun i => (hW.1 i).1) hW.2 h

/-- `m ≈_{w̄} τ` is, definitionally, `weightedBias w m τ → 0` (FAF's `weightedBias`,
`Properties/Support/WeightedAverages.lean`): the form `BoundedSequence.recurringunbiasednessexp`
and the `wubexp` family conclude in.
Source: [[theorem-ss-streamlined]] §1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem weightedApprox_iff_weightedBias {w m τ : ℕ → ℝ} :
    WeightedApprox w m τ ↔ Tendsto (weightedBias w m τ) atTop (𝓝 0) :=
  Iff.rfl

/-! ### The exclusive Cesàro mean and its bridge -/

/-- `cesaro x N = weightedAverage 1 x (N - 1)` for `N ≥ 1`: the exclusive Cesàro mean is FAF's
uniform weighted average one day earlier (inclusive `prefixSum` versus exclusive `range N`).
Source: anson-052
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem cesaro_eq_weightedAverage_one (x : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    cesaro x N = weightedAverage (fun _ => 1) x (N - 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hden : prefixSum (fun _ : ℕ => (1 : ℝ)) M = (M : ℝ) + 1 := by
    rw [prefixSum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    ring
  rw [weightedAverage_eq_div (by rw [hden]; positivity), hden, cesaro]
  simp only [prefixSum, one_mul]
  push_cast
  ring

/-- Mathlib's `Filter.Tendsto.cesaro` in the `cesaro` spelling: `x → l` gives `cesaro x → l`.
Source: anson-052
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem tendsto_cesaro {x : ℕ → ℝ} {l : ℝ} (h : Tendsto x atTop (𝓝 l)) :
    Tendsto (cesaro x) atTop (𝓝 l) := by
  refine h.cesaro.congr (fun n => ?_)
  simp [cesaro, div_eq_inv_mul]

/-! ### A3. Kronecker's lemma -/

/-- Abel-type identity behind Kronecker: with `s N = ∑_{n<N} x n / b n`,
`∑_{n<N} x n = b N * s N - ∑_{n<N} (b (n+1) - b n) * s (n+1)`.
Source: none: infrastructure (FAF `prefixSum_mul_eq_abel` is the inclusive analogue)
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma kronecker_identity {b x s : ℕ → ℝ} (hb : ∀ n, b n ≠ 0) (hs0 : s 0 = 0)
    (hs : ∀ n, s (n + 1) = s n + x n / b n) (N : ℕ) :
    ∑ n ∈ range N, x n =
      b N * s N - ∑ n ∈ range N, (b (n + 1) - b n) * s (n + 1) := by
  induction N with
  | zero => simp [hs0]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, hs N]
    have := hb N
    field_simp
    ring

/-- **Kronecker's lemma** (A3), conditional form: `b` positive, monotone, `→ ∞`, and the partial
sums `∑_{n<N} x n / b n` **converge** (no `Summable`, which for real series is absolute
convergence) ⟹ `(∑_{n<N} x n) / b N → 0`. Absent from Mathlib (grep 2026-09-29). Proof: the
Abel identity `kronecker_identity` writes the quotient as `s N - (mass/b N) · weightedAverage`
of the shifted partial sums under the weighting `b (n+1) - b n`, and the donor rule sends the
average to the same limit as `s`.
Source: anson-052 (`dose-response.md` §4, Prop 4.1); [[li-asymp-calc-mandate]] A3
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem kronecker {b x : ℕ → ℝ} (hb : ∀ n, 0 < b n) (hmono : Monotone b)
    (hdiv : Tendsto b atTop atTop) {L : ℝ}
    (hconv : Tendsto (fun N => ∑ n ∈ range N, x n / b n) atTop (𝓝 L)) :
    Tendsto (fun N => (∑ n ∈ range N, x n) / b N) atTop (𝓝 0) := by
  set s : ℕ → ℝ := fun N => ∑ n ∈ range N, x n / b n with hs_def
  have hs0 : s 0 = 0 := by simp [hs_def]
  have hs : ∀ n, s (n + 1) = s n + x n / b n := fun n => by
    simp [hs_def, Finset.sum_range_succ]
  set w : ℕ → ℝ := fun n => b (n + 1) - b n with hw_def
  have hw : ∀ i, 0 ≤ w i := fun i => sub_nonneg.2 (hmono (Nat.le_succ i))
  have hpre : ∀ M, prefixSum w M = b (M + 1) - b 0 := by
    intro M
    induction M with
    | zero => simp [prefixSum, hw_def]
    | succ M ih =>
      rw [prefixSum_succ, ih]
      simp only [hw_def]
      ring
  have hb1 : Tendsto (fun M => b (M + 1)) atTop atTop := hdiv.comp (tendsto_add_atTop_nat 1)
  have hwdiv : Tendsto (prefixSum w) atTop atTop := by
    refine (tendsto_atTop_add_const_right atTop (-b 0) hb1).congr (fun M => ?_)
    rw [hpre M]
    ring
  have hs1 : Tendsto (fun M => s (M + 1)) atTop (𝓝 L) := hconv.comp (tendsto_add_atTop_nat 1)
  have hwavg : Tendsto (weightedAverage w (fun n => s (n + 1))) atTop (𝓝 L) :=
    weightedAverage_tendsto hw hwdiv hs1
  have hratio : Tendsto (fun M => prefixSum w M / b (M + 1)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun M => b 0 / b (M + 1)) atTop (𝓝 0) := hb1.const_div_atTop (b 0)
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub h0
    rw [sub_zero] at this
    refine this.congr (fun M => ?_)
    rw [hpre M, sub_div, div_self (hb (M + 1)).ne']
  have hmain : Tendsto (fun M => s (M + 1) - prefixSum w M / b (M + 1) *
      weightedAverage w (fun n => s (n + 1)) M) atTop (𝓝 0) := by
    have := hs1.sub (hratio.mul hwavg)
    simpa using this
  rw [← tendsto_add_atTop_iff_nat 1]
  refine hmain.congr' ?_
  filter_upwards [eventually_prefixSum_pos hwdiv] with M hM
  have hid := kronecker_identity (fun n => (hb n).ne') hs0 hs (M + 1)
  have hsum : ∑ n ∈ range (M + 1), (b (n + 1) - b n) * s (n + 1) =
      prefixSum (fun n => w n * s (n + 1)) M := rfl
  rw [weightedAverage_eq_div hM.ne', hid, hsum]
  have hbM := (hb (M + 1)).ne'
  have hpM := hM.ne'
  field_simp

/-- Kronecker in FAF's inclusive `prefixSum` spelling: if `prefixSum (x / b)` converges then
`prefixSum x N / b N → 0`.
Source: anson-052; [[li-asymp-calc-mandate]] A3
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem kronecker_prefixSum {b x : ℕ → ℝ} (hb : ∀ n, 0 < b n) (hmono : Monotone b)
    (hdiv : Tendsto b atTop atTop) {L : ℝ}
    (hconv : Tendsto (prefixSum (fun n => x n / b n)) atTop (𝓝 L)) :
    Tendsto (fun N => prefixSum x N / b N) atTop (𝓝 0) := by
  have hconv' : Tendsto (fun N => ∑ n ∈ range N, x n / b n) atTop (𝓝 L) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    exact hconv
  have h1 := kronecker hb hmono hdiv hconv'
  have hterm : Tendsto (fun N => x N / b N) atTop (𝓝 0) := by
    have := (hconv'.comp (tendsto_add_atTop_nat 1)).sub hconv'
    rw [sub_self] at this
    refine this.congr (fun N => ?_)
    simp [Function.comp, Finset.sum_range_succ]
  have := h1.add hterm
  rw [add_zero] at this
  refine this.congr (fun N => ?_)
  rw [prefixSum, Finset.sum_range_succ, add_div]

/-- **Kronecker witness (N+)**: `x n = (-1)^n`, `b n = n + 1`. The partial sums of `x n / b n`
converge (alternating series) while the series is **not** summable in `ℝ` (absolute convergence
would make the harmonic series summable), so the conditional hypothesis of `kronecker` is
strictly more general than `Summable`, as `def-dose-response`'s martingale use needs.
Source: [[li-asymp-calc-mandate]] A3
Kind: N+
Fidelity: n/a
Hyps: n/a -/
theorem kronecker_witness_conditional :
    (∃ L, Tendsto (fun N => ∑ n ∈ range N, (-1 : ℝ) ^ n / ((n : ℝ) + 1)) atTop (𝓝 L)) ∧
    ¬ Summable (fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1)) := by
  constructor
  · have hanti : Antitone (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
      intro m n hmn
      apply one_div_le_one_div_of_le
      · positivity
      · have : (m : ℝ) ≤ n := by exact_mod_cast hmn
        linarith
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨l, hl⟩ := hanti.tendsto_alternating_series_of_tendsto_zero h0
    refine ⟨l, hl.congr (fun N => Finset.sum_congr rfl (fun n _ => ?_))⟩
    ring
  · intro hsum
    have habs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
      refine hsum.abs.congr (fun n => ?_)
      rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (by positivity)]
    have h2 : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) :=
      habs.congr (fun n => by push_cast; rfl)
    exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).1 h2)

/-- Kronecker witness, the positive half in the exact hypothesis shape of `kronecker`: the
weighting `b n = n + 1` is positive, monotone and divergent.
Source: [[li-asymp-calc-mandate]] A3
Kind: N+
Fidelity: n/a
Hyps: n/a -/
theorem kronecker_witness_weighting :
    (∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1) ∧ Monotone (fun n : ℕ => (n : ℝ) + 1) ∧
      Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
  refine ⟨fun n => by positivity, fun m n hmn => ?_, ?_⟩
  · have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    simp only
    linarith
  · exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

end Cleanroom.Found.LiAsympCalc
