import Cleanroom.Deference.DefDoseResponse.Defs
import Cleanroom.Li.LiPseudorandom.Defs
import Cleanroom.Found.LiQuoteLane.Feature
import LogicalInduction.Construction.Quotation.DeferralFibre
import LogicalInduction.Properties.Pseudorandomness

/-!
# `def-dose-response` · Sampling: Lemma 4.2 (the Sampling Lemma) and Cor T1.2 (T4)

**Lemma 4.2** (note §4): for a coin `c` pseudorandom with frequency `p` relative to the market `P`
(FAF's `PseudorandomFrequency (truthR c) p f P`), any P-generable divergent `f`-patient weighting
`W` and any P-generable `[−1,1]`-valued feature `X`,
`∑_{n≤N} w_n c_n x_n = p ∑_{n≤N} w_n x_n + o(∑_{n≤N} w_n)`. The exposed subsequence is a faithful
sample of the committed stream on every nameable pattern — "commit-then-reveal, as mathematics",
the epistemological core of the design, which the zip left with no kernel content (zip AUDIT §3.7).

Proof as in the note: split `x = x⁺ − x⁻` with `x^± := max(0, ±x)` (features: `EF.max` with
`EF.const 0`, `EF.mul (EF.const (−1))`; P-generable by `PGenerableWeighting.max'`, proved here
from FAF's `serialize_max`); for each half, `W·x^±` is a P-generable `[0,1]` weighting
(`PGenerableWeighting.mul`), `f`-patient (`DeferralPatient.mul_le_one`); on the divergent branch
pseudorandomness applies to it and the `o(∑ w x^±)` is `o(∑ w)` since `x^± ≤ 1`; on the
bounded branch both sides are `O(1)`. The analytic core is `half_sampling`, stated over real
sequences.

**Cor T1.2**: at `x ≡ 1` the sampling identity is pseudorandomness itself
(`representative_subsample_count`); for a `[0,1]`-feature `x` and `p > 0`, the exposed-day gated
average of `x` differs from the all-day gated average by `o(1)` (`representative_subsample`).

The weightings quantified over are FAF's class (all P-generable weightings of `P`), rendering the
note's "pre-coin `𝒞_A`-generable"; the hypothesis `PseudorandomFrequency` is FAF's definition and
quantifies over the *same* class, so the class enters both sides and this is a rendering, not a
strengthening on that axis (fidelity audit r2 N1: no comparison of FAF's price-feature class with
the note's class is established here). The `f`-patience hypothesis on `W` is FAF's (LI 4.4.2's),
not in the note's Lemma 4.2 wording. The `[−1,1]` bound on `x` is load-bearing (with `x`
unbounded the lemma is false), kept in the statement. Grade (a) throughout. Scope: one-way.
-/

namespace Cleanroom.Deference.DefDoseResponse

open LogicalInduction Cleanroom.Li.LiPseudorandom Cleanroom.Found.LiQuoteLane
open Filter Topology Finset

/-! ## Closure of P-generable weightings under `max` -/

/-- P-generable weightings are closed under `EF.max` (FAF's `serialize_max`; the rank and
closure clauses as for `PGenerableWeighting.mul`).
Source: none: infrastructure (FAF `PGenerableWeighting.mul`, `PairedWeighting.max`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem PGenerableWeighting.max' {A B : ℕ → EF} (hA : PGenerableWeighting A)
    (hB : PGenerableWeighting B) : PGenerableWeighting (fun n => EF.max (A n) (B n)) where
  polySeg := MachineSpliceStream.serialize_max hA.polySeg hB.polySeg
  rank_le := by
    intro n
    simp only [EF.rank]
    exact Nat.max_le.mpr ⟨hA.rank_le n, hB.rank_le n⟩
  closed := by
    intro n ρ V
    simp only [EF.denoteWith, EF.denote_max]
    rw [hA.closed n ρ V, hB.closed n ρ V]

/-- The positive part `x⁺ := max(0, x)` of a feature progression.
Source: [[dose-response]] §4 Lemma 4.2 proof ("split `x = x⁺ − x⁻`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def posPart (X : ℕ → EF) (n : ℕ) : EF := EF.max (EF.const 0) (X n)

/-- The negative part `x⁻ := max(0, −x)`.
Source: [[dose-response]] §4 Lemma 4.2 proof
Kind: D
Fidelity: exact
Hyps: n/a -/
def negPart (X : ℕ → EF) (n : ℕ) : EF := EF.max (EF.const 0) (EF.mul (EF.const (-1)) (X n))

/-- `posPart_denote`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma posPart_denote (X : ℕ → EF) (n : ℕ) (P : History) :
    (posPart X n).denote P = max 0 ((X n).denote P) := by
  simp [posPart, EF.denote_max]

/-- `negPart_denote`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma negPart_denote (X : ℕ → EF) (n : ℕ) (P : History) :
    (negPart X n).denote P = max 0 (-(X n).denote P) := by
  simp [negPart, EF.denote_max, EF.denote_mul]

/-- The two parts are P-generable when the feature is.
Source: [[dose-response]] §4 Lemma 4.2 proof ("`x^± ∈ [0,1]` generable")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem posPart_pgenerable {X : ℕ → EF} (hX : PGenerableWeighting X) :
    PGenerableWeighting (posPart X) :=
  PGenerableWeighting.max' (pgenerableWeighting_const 0) hX

/-- `negPart_pgenerable`.
Source: [[dose-response]] §4 Lemma 4.2 proof
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem negPart_pgenerable {X : ℕ → EF} (hX : PGenerableWeighting X) :
    PGenerableWeighting (negPart X) :=
  PGenerableWeighting.max' (pgenerableWeighting_const 0)
    (PGenerableWeighting.mul (pgenerableWeighting_const (-1)) hX)

/-! ## Patience and divergence of a thinned weighting -/

/-- A product of an `f`-patient weighting by a `[0,1]`-valued feature is `f`-patient.
Source: [[dose-response]] §4 Lemma 4.2 proof ("`wx^± ∈ 𝒮*`" — the product closure)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem DeferralPatient.mul_le_one {f : DeferralFunction} {W Y : ℕ → EF} {P : History}
    (hpat : DeferralPatient f W P) (hW : ∀ n, 0 ≤ (W n).denote P)
    (hY : ∀ n, 0 ≤ (Y n).denote P ∧ (Y n).denote P ≤ 1) :
    DeferralPatient f (fun n => EF.mul (W n) (Y n)) P := by
  obtain ⟨C, hC⟩ := hpat
  refine ⟨C, fun n => le_trans ?_ (hC n)⟩
  refine Finset.sum_le_sum fun i _ => ?_
  rw [EF.denote_mul, Pi.mul_apply]
  exact mul_le_of_le_one_right (hW i) (hY i).2

/-- Prefix sums of a nonnegative sequence are monotone.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem prefixSum_monotone {x : ℕ → ℝ} (hx : ∀ n, 0 ≤ x n) : Monotone (prefixSum x) :=
  monotone_nat_of_le_succ fun n => by rw [prefixSum_succ]; linarith [hx (n + 1)]

/-- Prefix sums of a nonnegative sequence are nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem prefixSum_nonneg {x : ℕ → ℝ} (hx : ∀ n, 0 ≤ x n) (n : ℕ) : 0 ≤ prefixSum x n :=
  Finset.sum_nonneg fun i _ => hx i

/-- Termwise domination transfers to prefix sums.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem prefixSum_le_prefixSum {x y : ℕ → ℝ} (h : ∀ n, x n ≤ y n) (n : ℕ) :
    prefixSum x n ≤ prefixSum y n :=
  Finset.sum_le_sum fun i _ => h i

/-- A monotone sequence that does not tend to `+∞` is bounded.
Source: none: infrastructure (Mathlib `tendsto_atTop_atTop_iff_of_monotone`)
Kind: L
Fidelity: n/a -/
theorem bounded_of_monotone_not_tendsto {x : ℕ → ℝ} (hmono : Monotone x)
    (h : ¬ Tendsto x atTop atTop) : ∃ b, ∀ n, x n ≤ b := by
  rw [tendsto_atTop_atTop_iff_of_monotone hmono] at h
  push Not at h
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun n => (hb n).le⟩

/-! ## The analytic core -/

/-- **The sampling identity for one half.** For a `[0,1]` weighting `w` with divergent mass, a
`[0,1]` sequence `y`, a `[0,1]` truth stream and `p ∈ [0,1]`: if the `w·y`-weighted truth
frequency tends to `p` whenever `w·y` has divergent mass, then
`(∑_{n≤N} w_n y_n truth_n − p ∑_{n≤N} w_n y_n)/∑_{n≤N} w_n → 0`. On the divergent branch the
error is `o(∑ w y) ⊆ o(∑ w)`; on the bounded branch both sides are `O(1)`.
Source: [[dose-response]] §4 Lemma 4.2 proof (the two branches)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem half_sampling {w y truth : ℕ → ℝ} {p : ℝ} (hw : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (hdiv : Tendsto (prefixSum w) atTop atTop) (hy : ∀ n, 0 ≤ y n ∧ y n ≤ 1)
    (htruth : ∀ n, 0 ≤ truth n ∧ truth n ≤ 1) (hp : 0 ≤ p ∧ p ≤ 1)
    (hps : Tendsto (prefixSum (fun n => w n * y n)) atTop atTop →
      weightedAverage (fun n => w n * y n) truth ≈ₙ fun _ => p) :
    Tendsto (fun N => (prefixSum (fun n => w n * y n * truth n) N -
      p * prefixSum (fun n => w n * y n) N) / prefixSum w N) atTop (𝓝 0) := by
  have hwy : ∀ n, 0 ≤ w n * y n ∧ w n * y n ≤ w n :=
    fun n => ⟨mul_nonneg (hw n).1 (hy n).1, mul_le_of_le_one_right (hw n).1 (hy n).2⟩
  have hwyt : ∀ n, 0 ≤ w n * y n * truth n ∧ w n * y n * truth n ≤ w n * y n :=
    fun n => ⟨mul_nonneg (hwy n).1 (htruth n).1, mul_le_of_le_one_right (hwy n).1 (htruth n).2⟩
  have hSpos : ∀ᶠ N in atTop, 0 < prefixSum w N := hdiv.eventually (eventually_gt_atTop 0)
  by_cases hd : Tendsto (prefixSum (fun n => w n * y n)) atTop atTop
  · have h := hps hd
    have hpos : ∀ᶠ N in atTop, 0 < prefixSum (fun n => w n * y n) N :=
      hd.eventually (eventually_gt_atTop 0)
    refine squeeze_zero_norm' ?_ (tendsto_zero_iff_norm_tendsto_zero.mp h)
    filter_upwards [hpos, hSpos] with N hN hS
    rw [weightedAverage_eq_div hN.ne']
    have hle : prefixSum (fun n => w n * y n) N ≤ prefixSum w N :=
      prefixSum_le_prefixSum (fun n => (hwy n).2) N
    have key : (prefixSum (fun n => w n * y n * truth n) N -
        p * prefixSum (fun n => w n * y n) N) / prefixSum w N =
        (prefixSum (fun i => w i * y i * truth i) N / prefixSum (fun n => w n * y n) N - p) *
          (prefixSum (fun n => w n * y n) N / prefixSum w N) := by
      field_simp
    rw [key]
    try simp only [Real.norm_eq_abs]
    rw [abs_mul]
    have hfrac : |prefixSum (fun n => w n * y n) N / prefixSum w N| ≤ 1 := by
      rw [abs_of_nonneg (div_nonneg hN.le hS.le), div_le_one hS]
      exact hle
    calc |prefixSum (fun i => w i * y i * truth i) N / prefixSum (fun n => w n * y n) N - p| *
          |prefixSum (fun n => w n * y n) N / prefixSum w N|
        ≤ |prefixSum (fun i => w i * y i * truth i) N / prefixSum (fun n => w n * y n) N - p| * 1 :=
          mul_le_mul_of_nonneg_left hfrac (abs_nonneg _)
      _ = _ := mul_one _
  · obtain ⟨b, hb⟩ := bounded_of_monotone_not_tendsto (prefixSum_monotone fun n => (hwy n).1) hd
    have hbound : ∀ N, |prefixSum (fun n => w n * y n * truth n) N -
        p * prefixSum (fun n => w n * y n) N| ≤ 2 * b := by
      intro N
      have h1 : 0 ≤ prefixSum (fun n => w n * y n * truth n) N :=
        prefixSum_nonneg (fun n => (hwyt n).1) N
      have h2 : prefixSum (fun n => w n * y n * truth n) N ≤ prefixSum (fun n => w n * y n) N :=
        prefixSum_le_prefixSum (fun n => (hwyt n).2) N
      have h3 : 0 ≤ prefixSum (fun n => w n * y n) N := prefixSum_nonneg (fun n => (hwy n).1) N
      have h4 := hb N
      rw [abs_le]
      constructor <;> nlinarith [hp.1, hp.2]
    have hlim : Tendsto (fun N => 2 * b / prefixSum w N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hdiv
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hSpos] with N hS
    try simp only [Real.norm_eq_abs]
    rw [abs_div, abs_of_pos hS]
    exact div_le_div_of_nonneg_right (hbound N) hS.le

/-! ## T4 — the Sampling Lemma over FAF -/

/-- **T4, Lemma 4.2 (the Sampling Lemma, headline).** For a coin `c` pseudorandom with frequency
`p ∈ [0,1]` relative to `P` at the deferral `f` (FAF's `PseudorandomFrequency`), any P-generable
weighting `W` divergent on `P` and `f`-patient, and any P-generable feature `X` with
`[−1,1]` values on `P`:
`(∑_{n≤N} w_n c_n x_n − p ∑_{n≤N} w_n x_n) / ∑_{n≤N} w_n → 0`. Scope: one-way.
Source: [[dose-response]] §4 Lemma 4.2; anson-050
Kind: C
Fidelity: exact (rendering): the note's "pre-coin `𝒞_A`-generable" as FAF's `PGenerableWeighting`, `𝒮*` as FAF's `PseudorandomFrequency` — the same class on both sides; `f`-patience on `W` as FAF requires (fidelity audit r2 N1)
Hyps: (a) none -/
theorem sampling_lemma {P : History} {c : ℕ → Bool} {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1)
    {f : DeferralFunction} (hps : PseudorandomFrequency (truthR c) p f P) {W : ℕ → EF}
    (hW : PGenerableWeighting W) (hdiv : DivergentWeighting W P) (hpat : DeferralPatient f W P)
    {X : ℕ → EF} (hX : PGenerableWeighting X)
    (hXb : ∀ n, -1 ≤ (X n).denote P ∧ (X n).denote P ≤ 1) :
    Tendsto (fun N => (prefixSum (fun n => (W n).denote P * truthR c n * (X n).denote P) N -
      p * prefixSum (fun n => (W n).denote P * (X n).denote P) N) /
        prefixSum (fun n => (W n).denote P) N) atTop (𝓝 0) := by
  have htruth : ∀ n, 0 ≤ truthR c n ∧ truthR c n ≤ 1 := by
    intro n; unfold truthR; split_ifs <;> norm_num
  have hw := hdiv.1
  -- the two halves
  have hhalf : ∀ (Y : ℕ → EF), PGenerableWeighting Y →
      (∀ n, 0 ≤ (Y n).denote P ∧ (Y n).denote P ≤ 1) →
      Tendsto (fun N => (prefixSum (fun n => (W n).denote P * (Y n).denote P * truthR c n) N -
        p * prefixSum (fun n => (W n).denote P * (Y n).denote P) N) /
          prefixSum (fun n => (W n).denote P) N) atTop (𝓝 0) := by
    intro Y hY hYb
    refine half_sampling hw hdiv.2 hYb htruth hp fun hd => ?_
    have hgen := PGenerableWeighting.mul hW hY
    have hdiv' : DivergentWeighting (fun n => EF.mul (W n) (Y n)) P := by
      refine ⟨fun n => ?_, ?_⟩
      · rw [EF.denote_mul, Pi.mul_apply]
        exact ⟨mul_nonneg (hw n).1 (hYb n).1, mul_le_one₀ (hw n).2 (hYb n).1 (hYb n).2⟩
      · refine hd.congr fun N => ?_
        unfold prefixSum
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [EF.denote_mul, Pi.mul_apply]
    have hpat' := DeferralPatient.mul_le_one hpat (fun n => (hw n).1) hYb
    have h := hps _ hgen hdiv' hpat'
    have heq : (fun i => (EF.mul (W i) (Y i)).denote P) = fun n => (W n).denote P * (Y n).denote P := by
      funext i; rw [EF.denote_mul, Pi.mul_apply]
    rw [heq] at h
    exact h
  have hpos := hhalf (posPart X) (posPart_pgenerable hX) (fun n => by
    rw [posPart_denote]; exact ⟨le_max_left _ _, max_le zero_le_one (hXb n).2⟩)
  have hneg := hhalf (negPart X) (negPart_pgenerable hX) (fun n => by
    rw [negPart_denote]; exact ⟨le_max_left _ _, max_le zero_le_one (by linarith [(hXb n).1])⟩)
  have hsub := hpos.sub hneg
  rw [sub_zero] at hsub
  refine hsub.congr fun N => ?_
  have hx : ∀ n, (X n).denote P = (posPart X n).denote P - (negPart X n).denote P := by
    intro n
    rw [posPart_denote, negPart_denote]
    rcases le_or_gt 0 ((X n).denote P) with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h.le, max_eq_right (by linarith)]; ring
  have e1 : prefixSum (fun n => (W n).denote P * truthR c n * (X n).denote P) N =
      prefixSum (fun n => (W n).denote P * (posPart X n).denote P * truthR c n) N -
        prefixSum (fun n => (W n).denote P * (negPart X n).denote P * truthR c n) N := by
    rw [← prefixSum_sub]
    unfold prefixSum
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [hx i]; ring
  have e2 : prefixSum (fun n => (W n).denote P * (X n).denote P) N =
      prefixSum (fun n => (W n).denote P * (posPart X n).denote P) N -
        prefixSum (fun n => (W n).denote P * (negPart X n).denote P) N := by
    rw [← prefixSum_sub]
    unfold prefixSum
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [hx i]; ring
  rw [e1, e2]
  ring

/-! ## Cor T1.2 — the representative subsample -/

/-- **Cor T1.2 (i), the count form**: `∑_{n≤N} w_n c_n = p ∑_{n≤N} w_n + o(∑_{n≤N} w_n)` — the
sampling identity at `x ≡ 1`, which is pseudorandomness itself.
Source: [[dose-response]] §5 Cor T1.2 ("`∑ g_n c_n = p ∑ g_n + o(∑ g_n)`"); anson-050
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem representative_subsample_count {P : History} {c : ℕ → Bool} {p : ℝ}
    {f : DeferralFunction} (hps : PseudorandomFrequency (truthR c) p f P) {W : ℕ → EF}
    (hW : PGenerableWeighting W) (hdiv : DivergentWeighting W P) (hpat : DeferralPatient f W P) :
    Tendsto (fun N => (prefixSum (fun n => (W n).denote P * truthR c n) N -
      p * prefixSum (fun n => (W n).denote P) N) / prefixSum (fun n => (W n).denote P) N)
      atTop (𝓝 0) := by
  have h := hps W hW hdiv hpat
  have hSpos : ∀ᶠ N in atTop, 0 < prefixSum (fun n => (W n).denote P) N :=
    hdiv.2.eventually (eventually_gt_atTop 0)
  refine (h.congr' ?_)
  filter_upwards [hSpos] with N hS
  rw [weightedAverage_eq_div hS.ne']
  field_simp

/-- **Cor T1.2 (ii), the representative subsample (headline).** For a pseudorandom coin of
frequency `p > 0`, a P-generable divergent patient weighting `w` and a P-generable `[0,1]`-feature
`x`: the exposed-day gated average `∑ w c x / ∑ w c` and the all-day gated average `∑ w x / ∑ w`
differ by `o(1)`. What the audit samples is what the policy was.
Source: [[dose-response]] §5 Cor T1.2 ("the exposed-day gated average of `x` differs from the all-day gated average by `o(1)`"); anson-050
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem representative_subsample {P : History} {c : ℕ → Bool} {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    {f : DeferralFunction} (hps : PseudorandomFrequency (truthR c) p f P) {W : ℕ → EF}
    (hW : PGenerableWeighting W) (hdiv : DivergentWeighting W P) (hpat : DeferralPatient f W P)
    {X : ℕ → EF} (hX : PGenerableWeighting X)
    (hXb : ∀ n, 0 ≤ (X n).denote P ∧ (X n).denote P ≤ 1) :
    Tendsto (fun N =>
      prefixSum (fun n => (W n).denote P * truthR c n * (X n).denote P) N /
        prefixSum (fun n => (W n).denote P * truthR c n) N -
      prefixSum (fun n => (W n).denote P * (X n).denote P) N /
        prefixSum (fun n => (W n).denote P) N) atTop (𝓝 0) := by
  set S : ℕ → ℝ := prefixSum (fun n => (W n).denote P) with hSdef
  set Sx : ℕ → ℝ := prefixSum (fun n => (W n).denote P * (X n).denote P) with hSxdef
  set Sc : ℕ → ℝ := prefixSum (fun n => (W n).denote P * truthR c n) with hScdef
  set Scx : ℕ → ℝ := prefixSum (fun n => (W n).denote P * truthR c n * (X n).denote P) with hScxdef
  have he1 : Tendsto (fun N => (Scx N - p * Sx N) / S N) atTop (𝓝 0) :=
    sampling_lemma ⟨hp0.le, hp1⟩ hps hW hdiv hpat hX (fun n => ⟨by linarith [(hXb n).1], (hXb n).2⟩)
  have he2 : Tendsto (fun N => (Sc N - p * S N) / S N) atTop (𝓝 0) :=
    representative_subsample_count hps hW hdiv hpat
  have hw := hdiv.1
  have hSpos : ∀ᶠ N in atTop, 0 < S N := hdiv.2.eventually (eventually_gt_atTop 0)
  -- the bounded ratio `Sx/S ∈ [0,1]`
  have hratio : ∀ N, 0 < S N → 0 ≤ Sx N / S N ∧ Sx N / S N ≤ 1 := by
    intro N hS
    refine ⟨div_nonneg (prefixSum_nonneg (fun n => mul_nonneg (hw n).1 (hXb n).1) N) hS.le, ?_⟩
    rw [div_le_one hS]
    exact prefixSum_le_prefixSum (fun n => mul_le_of_le_one_right (hw n).1 (hXb n).2) N
  -- `e₂ · (Sx/S) → 0`
  have hprod : Tendsto (fun N => (Sc N - p * S N) / S N * (Sx N / S N)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_zero_iff_norm_tendsto_zero.mp he2)
    filter_upwards [hSpos] with N hS
    try simp only [Real.norm_eq_abs]
    rw [abs_mul]
    have := hratio N hS
    calc |(Sc N - p * S N) / S N| * |Sx N / S N|
        ≤ |(Sc N - p * S N) / S N| * 1 :=
          mul_le_mul_of_nonneg_left (by rw [abs_of_nonneg this.1]; exact this.2) (abs_nonneg _)
      _ = _ := mul_one _
  -- the denominator `Sc/S = p + e₂ → p ≠ 0`
  have hden : Tendsto (fun N => Sc N / S N) atTop (𝓝 p) := by
    have h1 := (tendsto_const_nhds (x := p)).add he2
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [hSpos] with N hS
    rw [eq_div_iff hS.ne', add_mul, div_mul_cancel₀ _ hS.ne']
    ring
  have hnum : Tendsto (fun N => (Scx N - p * Sx N) / S N - (Sc N - p * S N) / S N * (Sx N / S N))
      atTop (𝓝 0) := by
    have := he1.sub hprod
    rwa [sub_zero] at this
  have hlim := hnum.div hden hp0.ne'
  rw [zero_div] at hlim
  refine hlim.congr' ?_
  -- eventually `Sc N > 0` and the algebraic identity holds
  have hScpos : ∀ᶠ N in atTop, 0 < Sc N := by
    have h := he2
    rw [Metric.tendsto_atTop] at h
    obtain ⟨N₀, hN₀⟩ := h (p / 2) (by linarith)
    filter_upwards [hSpos, eventually_ge_atTop N₀] with N hS hN
    have h1 := hN₀ N hN
    rw [Real.dist_eq, sub_zero, abs_lt] at h1
    have h2 : (Sc N - p * S N) / S N > -(p / 2) := h1.1
    rw [gt_iff_lt, lt_div_iff₀ hS] at h2
    nlinarith
  filter_upwards [hSpos, hScpos] with N hS hSc
  simp only [Pi.div_apply]
  have hS' := hS.ne'
  have hSc' := hSc.ne'
  rw [div_eq_iff (div_ne_zero hSc' hS')]
  field_simp
  ring

end Cleanroom.Deference.DefDoseResponse
