import Cleanroom.Found.LiAsympCalc.Density
import Mathlib.Data.Nat.Sqrt

/-!
# H1. Averaging hides spikes: running sup, Markov, and the spike frequency

Target H1 of [[li-asymp-calc-mandate]] (trust-lab-043, 2-045:
`research/deference-trust-lab/run2/lean/averaging-hides-spikes.lean`), titled as **gap-closure**
as the source asks:

* (i) for `a ≥ 0`, `runningSup a → 0` iff `a ≡ 0` — the running sup carries no averaging;
* (ii) the spike family `spike B k` has Cesàro mean `→ 0` and running sup `= B` from day `k`;
* (iii) the near-miss "`a ≤ c`, `c → 0` ⟹ `runningSup a → 0`" is **false** (stated as a negation);
* (iv) Markov: a uniform bound on the partial sums bounds the number of `ε`-spikes by `S/ε`, with
  a tightness family attaining the bound;
* (v) `cesaro a → 0` ⟹ the `ε`-spike frequency `countIn {ε ≤ a} N / N → 0`, with a witness having
  infinitely many spikes (at the squares).
-/

namespace Cleanroom.Found.LiAsympCalc

open LogicalInduction Filter Topology Finset

/-! ### Running sup basics -/

/-- `a i ≤ runningSup a T` for `i ≤ T`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma le_runningSup (a : ℕ → ℝ) {i T : ℕ} (h : i ≤ T) : a i ≤ runningSup a T :=
  Finset.le_sup' a (Finset.mem_range.2 (by omega))

/-- `runningSup a T ≤ b ↔ ∀ i ≤ T, a i ≤ b`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma runningSup_le_iff {a : ℕ → ℝ} {T : ℕ} {b : ℝ} :
    runningSup a T ≤ b ↔ ∀ i, i ≤ T → a i ≤ b := by
  unfold runningSup
  rw [Finset.sup'_le_iff]
  constructor
  · intro h i hi
    exact h i (Finset.mem_range.2 (by omega))
  · intro h i hi
    exact h i (by have := Finset.mem_range.1 hi; omega)

/-- `0 ≤ runningSup a T` when `a ≥ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma runningSup_nonneg {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (T : ℕ) : 0 ≤ runningSup a T :=
  (ha 0).trans (le_runningSup a (Nat.zero_le T))

/-- The running sup is monotone in `T`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma runningSup_mono (a : ℕ → ℝ) : Monotone (runningSup a) := by
  intro S T hST
  unfold runningSup
  have hsub : Finset.range (S + 1) ⊆ Finset.range (T + 1) := fun x hx =>
    Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) (by omega))
  exact Finset.sup'_mono a hsub _

/-! ### (i) The running sup tends to `0` only for the zero sequence -/

/-- **Gap-closure (i)**: for `a ≥ 0`, `runningSup a → 0` iff `a i = 0` for every `i`.
Source: trust-lab-2-045 (`averaging-hides-spikes.lean`)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem tendsto_runningSup_zero_iff {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) :
    Tendsto (runningSup a) atTop (𝓝 0) ↔ ∀ i, a i = 0 := by
  constructor
  · intro h i
    by_contra hne
    have hpos : 0 < a i := lt_of_le_of_ne (ha i) (Ne.symm hne)
    have hev := h.eventually (gt_mem_nhds hpos)
    obtain ⟨T, hT1, hT2⟩ := (hev.and (eventually_ge_atTop i)).exists
    linarith [le_runningSup a hT2]
  · intro h
    have hzero : runningSup a = fun _ => 0 := by
      funext T
      apply le_antisymm
      · exact runningSup_le_iff.2 (fun i _ => (h i).le)
      · exact runningSup_nonneg ha T
    rw [hzero]
    exact tendsto_const_nhds

/-! ### (ii) The spike family -/

/-- A single spike of height `B` on day `k`.
Source: trust-lab-2-045
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def spike (B : ℝ) (k i : ℕ) : ℝ := if i = k then B else 0

/-- The Cesàro mean of a single spike tends to `0`.
Source: trust-lab-2-045
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem tendsto_cesaro_spike (B : ℝ) (k : ℕ) : Tendsto (cesaro (spike B k)) atTop (𝓝 0) := by
  refine (tendsto_const_div_atTop_nhds_zero_nat B).congr' ?_
  filter_upwards [eventually_gt_atTop k] with N hN
  unfold cesaro spike
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.2 hN)]

/-- The running sup of a spike of height `B ≥ 0` is `B` from day `k` on.
Source: trust-lab-2-045
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem runningSup_spike {B : ℝ} (hB : 0 ≤ B) {k T : ℕ} (hT : k ≤ T) :
    runningSup (spike B k) T = B := by
  apply le_antisymm
  · exact runningSup_le_iff.2 (fun i _ => by
      unfold spike
      split_ifs <;> linarith)
  · have := le_runningSup (spike B k) hT
    simpa [spike] using this

/-- **Gap-closure (ii)**: the spike family — Cesàro mean `→ 0`, running sup `= B` from day `k`.
Source: trust-lab-2-045
Kind: N+
Fidelity: exact
Hyps: n/a -/
theorem spike_family {B : ℝ} (hB : 0 ≤ B) (k : ℕ) :
    Tendsto (cesaro (spike B k)) atTop (𝓝 0) ∧ ∀ T, k ≤ T → runningSup (spike B k) T = B :=
  ⟨tendsto_cesaro_spike B k, fun _ hT => runningSup_spike hB hT⟩

/-! ### (iii) The near-miss is false -/

/-- **Gap-closure (iii)**: "`0 ≤ a ≤ c` and `c → 0` imply `runningSup a → 0`" is **false**:
`a = c = spike 1 0` refutes it. This re-proves, over the package's `runningSup` (`Finset.sup'`)
and in the universally quantified `¬ ∀` form, the source's own refutation
`running_sup_near_miss_false` (`averaging-hides-spikes.lean:148`): the source never put the
running-sup near-miss forward as a lemma — it states the true per-round form and refutes the
running-sup form itself — so there is no error in the source (audit round 1, B1).
Source: trust-lab-043 (`averaging-hides-spikes.lean` §(ii), `running_sup_near_miss_false`); trust-lab-2-045 (i)
Kind: L
Fidelity: exact (the negation of the near-miss, generalised to `∀ a c`)
Hyps: (a) none -/
theorem not_runningSup_tendsto_of_le :
    ¬ ∀ (a c : ℕ → ℝ), (∀ i, 0 ≤ a i) → (∀ i, a i ≤ c i) → Tendsto c atTop (𝓝 0) →
      Tendsto (runningSup a) atTop (𝓝 0) := by
  intro h
  have hnn : ∀ i, 0 ≤ spike 1 0 i := fun i => by
    unfold spike
    split_ifs <;> norm_num
  have hc : Tendsto (spike 1 0) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (eventually_atTop.2 ⟨1, fun i hi => by
      unfold spike
      rw [if_neg (by omega)]⟩)
  have := (tendsto_runningSup_zero_iff hnn).1 (h (spike 1 0) (spike 1 0) hnn (fun _ => le_rfl) hc) 0
  simp [spike] at this

/-! ### (iv) Markov -/

open Classical in
/-- `ε · #{i < N : ε ≤ a i} ≤ ∑_{i<N} a i` for `a ≥ 0`.
Source: trust-lab-2-045
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem countIn_mul_le_sum {a : ℕ → ℝ} {ε : ℝ} (ha : ∀ i, 0 ≤ a i) (N : ℕ) :
    (countIn {i | ε ≤ a i} N : ℝ) * ε ≤ ∑ i ∈ range N, a i := by
  rw [countIn_eq_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  simp only [Set.mem_setOf_eq]
  split_ifs with h
  · linarith
  · simp [ha i]

/-- **Gap-closure (iv), Markov**: if every partial sum of `a ≥ 0` is `≤ S`, then at most `S/ε`
days carry an `ε`-spike. One step from the indicator bound `countIn_mul_le_sum`, which is the
content.
Source: trust-lab-2-045
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem markov_countIn {a : ℕ → ℝ} {S ε : ℝ} (ha : ∀ i, 0 ≤ a i)
    (hS : ∀ N, ∑ i ∈ range N, a i ≤ S) (hε : 0 < ε) (N : ℕ) :
    (countIn {i | ε ≤ a i} N : ℝ) ≤ S / ε := by
  rw [le_div_iff₀ hε]
  exact (countIn_mul_le_sum ha N).trans (hS N)

/-- Tightness family for Markov: `ε` on the first `m` days, `0` afterwards.
Source: trust-lab-2-045
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def tightSpikes (ε : ℝ) (m i : ℕ) : ℝ := if i < m then ε else 0

/-- **Markov is tight**: `tightSpikes ε m` has partial sums `≤ m ε` and exactly `m = (m ε)/ε`
days with an `ε`-spike once `N ≥ m`.
Source: trust-lab-2-045
Kind: N+
Fidelity: exact
Hyps: n/a -/
theorem markov_tight {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    (∀ i, 0 ≤ tightSpikes ε m i) ∧
      (∀ N, ∑ i ∈ range N, tightSpikes ε m i ≤ m * ε) ∧
      ∀ N, m ≤ N → (countIn {i | ε ≤ tightSpikes ε m i} N : ℝ) = (m * ε) / ε := by
  classical
  refine ⟨fun i => by unfold tightSpikes; split_ifs <;> linarith, fun N => ?_, fun N hN => ?_⟩
  · calc ∑ i ∈ range N, tightSpikes ε m i
        ≤ ∑ i ∈ range N, (if i < m then ε else 0) := le_of_eq rfl
      _ = ∑ i ∈ (range N).filter (fun i => i < m), ε := by rw [Finset.sum_filter]
      _ ≤ ∑ i ∈ range m, ε := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi
            simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
            exact hi.2
          · intro i _ _
            exact hε.le
      _ = m * ε := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · rw [mul_div_cancel_right₀ _ hε.ne', countIn_eq_sum]
    trans (∑ i ∈ range N, if i < m then (1 : ℝ) else 0)
    · apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i < m
      · rw [if_pos (by simp [tightSpikes, hi]), if_pos hi]
      · rw [if_neg (by simp [tightSpikes, hi, hε]), if_neg hi]
    rw [Finset.sum_boole]
    have hfilt : (range N).filter (fun i => i < m) = range m := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hfilt, Finset.card_range]

/-! ### (v) Spike frequency under a vanishing Cesàro mean -/

/-- **Gap-closure (v)**: `cesaro a → 0` (with `a ≥ 0`) ⟹ the frequency of `ε`-spikes below `N`
tends to `0`. A squeeze through `countIn_mul_le_sum` (the content); graded `L` as the mandate
assigns `P` to (i) only.
Source: trust-lab-2-045
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem tendsto_spikeFrequency_zero {a : ℕ → ℝ} {ε : ℝ} (ha : ∀ i, 0 ≤ a i) (hε : 0 < ε)
    (h : Tendsto (cesaro a) atTop (𝓝 0)) :
    Tendsto (fun N => (countIn {i | ε ≤ a i} N : ℝ) / N) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N => cesaro a N / ε) atTop (𝓝 0) := by
    simpa using h.div_const ε
  refine squeeze_zero' (Eventually.of_forall (fun N => by positivity)) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_div_iff₀ hNR hε, cesaro, div_mul_cancel₀ _ hNR.ne']
  exact countIn_mul_le_sum ha N

/-- Spikes at the perfect squares: `1` at `k * k`, `0` elsewhere.
Source: trust-lab-2-045
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def squareSpikes (i : ℕ) : ℝ := if IsSquare i then 1 else 0

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma sum_squareSpikes_le (N : ℕ) : ∑ i ∈ range N, squareSpikes i ≤ (Nat.sqrt N : ℝ) + 1 := by
  classical
  have hsum : ∑ i ∈ range N, squareSpikes i = (((range N).filter IsSquare).card : ℝ) := by
    unfold squareSpikes
    rw [Finset.sum_boole]
  rw [hsum]
  have hsub : (range N).filter IsSquare ⊆ (range (Nat.sqrt N + 1)).image (fun k => k * k) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨k, hk⟩ := hi.2
    simp only [Finset.mem_image, Finset.mem_range]
    refine ⟨k, ?_, hk.symm⟩
    have hkk : k * k ≤ N := by
      rw [← hk]
      exact hi.1.le
    exact Nat.lt_succ_of_le (Nat.le_sqrt.2 hkk)
  have hcard := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Finset.card_range] at hcard
  exact_mod_cast hcard

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma tendsto_natSqrt_atTop : Tendsto Nat.sqrt atTop atTop :=
  tendsto_atTop_atTop_of_monotone (fun _ _ h => Nat.sqrt_le_sqrt h)
    (fun b => ⟨b * b, by rw [Nat.sqrt_eq]⟩)

/-- **(v) witness (N+)**: the square spikes have infinitely many spikes (`squareSpikes (k*k) = 1`
for every `k`) yet Cesàro mean `→ 0` (at most `√N + 1` squares below `N`).
Source: trust-lab-2-045
Kind: N+
Fidelity: exact
Hyps: n/a -/
theorem squareSpikes_witness :
    (∀ i, 0 ≤ squareSpikes i) ∧ (∀ k, squareSpikes (k * k) = 1) ∧
      Tendsto (cesaro squareSpikes) atTop (𝓝 0) := by
  refine ⟨fun i => by unfold squareSpikes; split_ifs <;> norm_num,
    fun k => by
      simp only [squareSpikes]
      rw [if_pos ⟨k, rfl⟩], ?_⟩
  have hlim : Tendsto (fun N : ℕ => (2 : ℝ) / (Nat.sqrt N : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat 2).comp tendsto_natSqrt_atTop
  refine squeeze_zero' (Eventually.of_forall (fun N => ?_)) ?_ hlim
  · unfold cesaro
    apply div_nonneg _ (Nat.cast_nonneg N)
    exact Finset.sum_nonneg (fun i _ => by unfold squareSpikes; split_ifs <;> norm_num)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hs : 1 ≤ Nat.sqrt N := by
      rw [Nat.le_sqrt]
      simpa using hN
    have hsR : (1 : ℝ) ≤ Nat.sqrt N := by exact_mod_cast hs
    have hNR : (0 : ℝ) < N := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
    have hss : ((Nat.sqrt N : ℕ) : ℝ) * (Nat.sqrt N : ℕ) ≤ N := by exact_mod_cast Nat.sqrt_le N
    unfold cesaro
    calc (∑ i ∈ range N, squareSpikes i) / N ≤ ((Nat.sqrt N : ℝ) + 1) / N :=
          div_le_div_of_nonneg_right (sum_squareSpikes_le N) hNR.le
      _ ≤ 2 / (Nat.sqrt N : ℝ) := by
          rw [div_le_div_iff₀ hNR (by linarith)]
          nlinarith

/-! ### C1 witness with infinitely many exceptions (lives here because it reuses `squareSpikes`) -/

/-- `0` at the perfect squares, `1` elsewhere: a `≤ 1` sequence with Cesàro mean `→ 1` and
infinitely many exceptions (`sqExc (k*k) = 0`) of density zero.
Source: [[li-asymp-calc-mandate]] C1 ("density-zero exceptions")
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def sqExc (n : ℕ) : ℝ := 1 - squareSpikes n

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma tendsto_cesaro_sqExc : Tendsto (cesaro sqExc) atTop (𝓝 1) := by
  have h0 := squareSpikes_witness.2.2
  have h1 : Tendsto (fun N => 1 - cesaro squareSpikes N) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub h0
  rw [sub_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNR : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  unfold cesaro sqExc
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    sub_div, div_self hNR]

/-- **Density witness (N+, infinitely many exceptions)**: the full hypothesis package of
`density_lemma` at `θ = 1/2`, `S = evens`, `d = 1/2`, with `x = sqExc`, which is `< 1/2` at
**infinitely many** `n ∈ S` (every even square `(2a)²`) and yet `≥ 1/2` frequently on `S`. So
the lemma's "infinitely often on `S`" is the sharp form: neither "eventually on `S`" nor
"everywhere on `S`" holds for this witness. Replaces the one-exception `density_witness`
(`Density.lean`, regraded N−) as the N+ witness of C1 (audit round 1, adversarial B2 (b)).
Source: [[li-asymp-calc-mandate]] C1
Kind: N+
Fidelity: n/a
Hyps: n/a -/
theorem density_witness_squares :
    (∀ n, sqExc n ≤ 1) ∧ Tendsto (cesaro sqExc) atTop (𝓝 1) ∧
      UpperDensityGE {n | Even n} (1 / 2) ∧
      (∃ᶠ n in atTop, n ∈ {n | Even n} ∧ sqExc n < 1 / 2) ∧
      (∃ᶠ n in atTop, n ∈ {n | Even n} ∧ (1 / 2 : ℝ) ≤ sqExc n) := by
  have hle : ∀ n, sqExc n ≤ 1 := fun n => by
    unfold sqExc squareSpikes; split_ifs <;> norm_num
  refine ⟨hle, tendsto_cesaro_sqExc, upperDensityGE_evens, ?_, ?_⟩
  · rw [frequently_atTop]
    intro a
    refine ⟨(2 * a) * (2 * a), by nlinarith, ?_, ?_⟩
    · exact (even_two_mul a).mul_right _
    · unfold sqExc
      rw [squareSpikes_witness.2.1 (2 * a)]
      norm_num
  · exact density_lemma (by norm_num) hle tendsto_cesaro_sqExc upperDensityGE_evens (by norm_num)

end Cleanroom.Found.LiAsympCalc
