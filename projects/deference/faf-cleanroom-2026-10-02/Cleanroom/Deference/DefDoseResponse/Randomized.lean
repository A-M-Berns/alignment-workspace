import Cleanroom.Deference.DefDoseResponse.Sampling
import Cleanroom.Deference.DefDoseResponse.Coin
import Cleanroom.Li.LiPseudorandom.Countable
import Cleanroom.Li.LiPseudorandom.AtomDP
import Cleanroom.Li.LiPseudorandom.Locality
import Cleanroom.Found.LiAsympCalc.WeightedAverage
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Process.Filtration
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# `def-dose-response` · Randomized: Prop 4.1, randomization justifies tameness (T5, proved)

The note's model (R): i.i.d. Bernoulli(`p`) coins. Over FAF: `coinMeasure p` is Mathlib's product
`Measure.infinitePi` of `bernoulliMeasure true false p` on `ℕ → Bool` (a probability measure), and
the claim is that for a **causal builder** `B` (the market's day-`n` prices read coins `j` with
`g j ≤ n` only, delay `∀ j, j < g j` — `li-pseudorandom`'s `CausalBuilder`), almost surely the
realized coin inhabits FAF's `PseudorandomFrequency` at every deferral relative to `B x`:

`randomization_justifies_tameness : ∀ᵐ x ∂(coinMeasure p), ∀ f, PseudorandomFrequency (truthR x) p f (B x)`.

**What is proved here (grade (a)).** The FAF packaging and the countable intersection:
`ae_pseudorandomFrequency_of_each` reduces the simultaneous statement to one a.s. statement *per*
P-generable weighting, through `li-pseudorandom`'s explicit enumeration `genWeighting` and its
coverage `genWeighting_covers` (`ae_all_iff` over `ℕ`); `DeferralPatient` is a hypothesis the
conclusion ignores, as in `pseudorandomFrequency_of_causal`. The a.s. event is not the empty event
(`coinMeasure_ae_exists`: the measure is a probability measure). The instance of record is FAF's
LIA over the process revealing the coin one day late (`lia_atomDP_randomized`,
`liaHistory_atomDP_causal`).

**The probabilistic core, split (repair round 1, fidelity B4) and closed (repair round 2).** The
weighted strong law `weighted_slln_causal` — for a causal builder and a P-generable `W`, almost
surely, if `W`'s realized mass on `B x` diverges then the `W`-weighted truth frequency tends to
`p` — is a *composition* of two pieces, both proved:

* **proved**: the Kronecker reduction `weightedAverage_asympEq_of_normalized_tendsto` (if the
  normalized centred sums `∑_{k≤N} w_k (t_k − p)/(1 + W_k)` converge and `W_N → ∞`, the weighted
  average tends to `p`; `li-asymp-calc`'s `kronecker_prefixSum` at `b_k := 1 + W_k`), and the
  predictability stone `weight_causal` / `normalizedWeight_measurable_piLE` (the day-`(n+1)`
  normalized weight is a function of the coins `≤ n`, measurable for Mathlib's `Filtration.piLE n`);
* **proved (repair round 2)**: `normalized_sum_tendsto_ae` — on every coin whose realized
  weights are `[0,1]`-valued, the normalized centred sums converge almost surely. It is
  `Coin.lean`'s `nmart_tendsto_ae` (the `L²`-martingale argument: martingale for `piLE` shifted
  by a day, `L²` norm `≤ 1` by the telescoping bound — whose first step `w_k² ≤ w_k` *is* the
  bound `0 ≤ w_k ≤ 1` — then `Submartingale.ae_tendsto_limitProcess`) applied to the **clamped**
  realized weights `clamp01 ((W n).denote (B x))` (the mandate's `w_n := clamp(…)`), which are
  predictable by `weight_causal`; on the coins whose realized weights are `[0,1]`-valued the
  clamp is the identity.

**The bound is load-bearing (repair round 2, B1 of both audits).** As split in repair round 1
the statement carried no bound: it quantified over every `PGenerableWeighting`, whose FAF data
(`def:ece`) has no sign and no `[0,1]` clause, and that statement was **false** — at the
sign-alternating weighting `altWeight` (`+1` on even days, `−1` on odd days, P-generable by the
`ifZero` certificate of `fa-theorem-a`'s `evenDays`) the normalizer is `2` or `1` and at `p = ½`
every normalized increment has absolute value `≥ ¼`, so the sums converge on **no** coin
(`normalized_sum_unbounded_false`, `normalized_sum_unbounded_statement_false`: the N+ rows of
record that the bound is needed; no junk division is involved — the adversarial audit's
sign-flipped variant refutes through the `x / 0 = 0` of a vanishing normalizer as well). The
bound now sits inside the a.s. implication, exactly where `weighted_slln_causal`'s
`DivergentWeighting` supplies it (`hdiv.1`); the divergence `W_N → ∞` stays with the Kronecker
reduction, the only place it is needed.

The delay `∀ j, j < g j` is load-bearing: at `g = id` the builder may read the day's coin and the
statement is false (`li-pseudorandom`'s `omniscient_not_causalBuilder_succ` is the record of
why); it is used through `weight_causal` — predictability of the clamped weights — and nowhere
else.

A version of T5 taking `M_N/W_N → 0` as a hypothesis would be kind S; none is stated. Status of
the headline: **proved**, grade (a) throughout (Mathlib's product measure, filtration,
conditional expectation and martingale convergence theorem; FAF's `prefixSum`;
`li-pseudorandom`'s `truthR`, `CausalBuilder` and `genWeighting`). No name in this module is
open (the four T5 names were removed from the open list in repair round 2).
-/

namespace Cleanroom.Deference.DefDoseResponse

open LogicalInduction Cleanroom.Li.LiPseudorandom Cleanroom.Found.LiAsympCalc MeasureTheory
  ProbabilityTheory
open Filter Topology

/-! ## The coin measure

`coinMeasure p` (Mathlib's `Measure.infinitePi` of `bernoulliMeasure true false p`), its
probability-measure instance and `coinMeasure_ae_exists` live in `Coin.lean` (moved there in
repair round 2, with the measurability stone `measurable_piLE_of_determined`). -/

/-- **The constant coin is a null event** (the mandate's non-degeneracy remark; adversarial audit
r1 N9): for `p < 1` the always-`true` coin has `coinMeasure p`-measure `0`, since it lies in every
cylinder `{x_0 = ⋯ = x_{N−1} = true}` of measure `p^N`. So T5's a.s. event is not inhabited only
by degenerate coins (by symmetry the same holds for the always-`false` coin at `p > 0`).
Source: mandate T5 ("exhibit that the constant coin has `μ`-measure `0`")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem coinMeasure_const_true_null (p : unitInterval) (hp : (p : ℝ) < 1) :
    coinMeasure p {x | ∀ n, x n = true} = 0 := by
  have hq1 : bernoulliMeasure true false p {true} < 1 := by
    rw [bernoulliMeasure_apply_of_mem_of_notMem p (measurableSet_singleton _)
      (Set.mem_singleton _) (by simp), ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_coe,
      unitInterval.coe_toNNReal, NNReal.coe_one]
    exact hp
  have hle : ∀ N : ℕ, coinMeasure p {x | ∀ n, x n = true} ≤
      (bernoulliMeasure true false p {true}) ^ N := by
    intro N
    have hsub : {x : ℕ → Bool | ∀ n, x n = true} ⊆
        Set.pi (↑(Finset.range N)) (fun _ => ({true} : Set Bool)) :=
      fun x hx i _ => hx i
    calc coinMeasure p {x | ∀ n, x n = true}
        ≤ coinMeasure p (Set.pi (↑(Finset.range N)) fun _ => ({true} : Set Bool)) :=
          measure_mono hsub
      _ = ∏ _i ∈ Finset.range N, bernoulliMeasure true false p {true} := by
          unfold coinMeasure
          exact Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)
      _ = (bernoulliMeasure true false p {true}) ^ N := by
          rw [Finset.prod_const, Finset.card_range]
  have htend : Tendsto (fun N : ℕ => (bernoulliMeasure true false p {true}) ^ N) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq1
  exact nonpos_iff_eq_zero.mp (ge_of_tendsto' htend hle)

/-! ## The probabilistic core: the Kronecker reduction (proved), the predictability of the
weights (proved), the normalized martingale's convergence (proved in repair round 2, from
`Coin.lean`) -/

/-- **The Kronecker reduction (deterministic, proved).** For nonnegative weights `w` with
divergent prefix sums, if the *normalized* centred sums
`∑_{n≤N} w_n (t_n − p) / (1 + W_n)` (`W_n := ∑_{i≤n} w_i`, FAF's inclusive `prefixSum`) converge
to some limit, then the `w`-weighted average of `t` tends to `p`. This is the deterministic half of
the weighted strong law: `li-asymp-calc`'s `kronecker_prefixSum` with `b_n := 1 + W_n`, then
`(1 + W_N)/W_N → 1`. What remains for `weighted_slln_causal` is purely probabilistic: that the
normalized centred sum converges almost surely (`normalized_sum_tendsto_ae`, OPEN).
Source: [[dose-response]] §4 Prop 4.1 proof (the Kronecker step); mandate T5 (3)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem weightedAverage_asympEq_of_normalized_tendsto {w t : ℕ → ℝ} {p : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hdiv : Tendsto (prefixSum w) atTop atTop) {L : ℝ}
    (hconv : Tendsto (prefixSum (fun n => w n * (t n - p) / (1 + prefixSum w n))) atTop
      (𝓝 L)) :
    weightedAverage w t ≈ₙ fun _ => p := by
  have hb : ∀ n, 0 < 1 + prefixSum w n := fun n => by
    have := prefixSum_nonneg hw n
    linarith
  have hmono : Monotone (fun n => 1 + prefixSum w n) := fun m n hmn => by
    have := prefixSum_monotone hw hmn
    simp only
    linarith
  have hbdiv : Tendsto (fun n => 1 + prefixSum w n) atTop atTop :=
    tendsto_atTop_add_const_left _ _ hdiv
  have hk : Tendsto (fun N => prefixSum (fun n => w n * (t n - p)) N / (1 + prefixSum w N))
      atTop (𝓝 0) :=
    kronecker_prefixSum (b := fun n => 1 + prefixSum w n) (x := fun n => w n * (t n - p))
      hb hmono hbdiv hconv
  have hratio : Tendsto (fun N => (1 + prefixSum w N) / prefixSum w N) atTop (𝓝 1) := by
    have h1 : Tendsto (fun N => 1 + (prefixSum w N)⁻¹) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp hdiv)
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [hdiv.eventually_gt_atTop 0] with N hN
    rw [add_div, div_self hN.ne', one_div, add_comm]
  have hprod := hk.mul hratio
  rw [zero_mul] at hprod
  show Tendsto (fun N => weightedAverage w t N - p) atTop (𝓝 0)
  refine hprod.congr' ?_
  filter_upwards [hdiv.eventually_gt_atTop 0] with N hN
  have hS : prefixSum (fun n => w n * (t n - p)) N =
      prefixSum (fun i => w i * t i) N - p * prefixSum w N := by
    unfold prefixSum
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h1 : 1 + prefixSum w N ≠ 0 := (hb N).ne'
  have h2 : prefixSum w N ≠ 0 := hN.ne'
  rw [weightedAverage_eq_div h2, hS]
  field_simp

/-- **The day-`n` weight reads the coins `< n` only** (predictability). For a causal builder with
delay `≥ 1` and a P-generable `W`, `(W n).denote (B x)` depends on `x_0, …, x_{n−1}`: the day-`n`
feature reads prices of days `≤ n` (`rank_le`, `PGenerableWeighting.denote_congr`), and those
prices read coins `j` with `g j ≤ n`, hence `j < n` (`CausalBuilder`, `j < g j`).
Source: [[dose-response]] §4 Prop 4.1 proof ("`w_n` is `𝓕_{n−1}`-measurable"); mandate T5 (3)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem weight_causal {B : (ℕ → Bool) → History} {g : ℕ → ℕ} (hB : CausalBuilder B g)
    (hg : ∀ j, j < g j) {W : ℕ → EF} (hW : PGenerableWeighting W) (n : ℕ) {x y : ℕ → Bool}
    (h : ∀ j < n, x j = y j) : (W n).denote (B x) = (W n).denote (B y) :=
  Cleanroom.Li.LiPseudorandom.PGenerableWeighting.denote_congr hW n
    (hB x y n fun j hj => h j (lt_of_lt_of_le (hg j) hj))

/-- **The normalized martingale increment is predictable**: the factor
`w_{n+1} / (1 + W_{n+1})` of the `(n+1)`-st centred increment is a function of the coins `≤ n`,
hence `piLE n`-measurable — the hypothesis the martingale property of
`∑ w_k (𝟙[x k] − p)/(1 + W_k)` needs at step `n+1` (its other factor, `𝟙[x (n+1)] − p`, is the
coin `n+1`, independent of `piLE n` under the product measure).
Source: [[dose-response]] §4 Prop 4.1 proof; mandate T5 (3)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem normalizedWeight_measurable_piLE {B : (ℕ → Bool) → History} {g : ℕ → ℕ}
    (hB : CausalBuilder B g) (hg : ∀ j, j < g j) {W : ℕ → EF} (hW : PGenerableWeighting W)
    (n : ℕ) :
    Measurable[MeasureTheory.Filtration.piLE n] (fun x =>
      (W (n + 1)).denote (B x) / (1 + prefixSum (fun i => (W i).denote (B x)) (n + 1))) := by
  refine measurable_piLE_of_determined n fun x y hxy => ?_
  have hw : ∀ i ≤ n + 1, (W i).denote (B x) = (W i).denote (B y) := fun i hi =>
    weight_causal hB hg hW i fun j hj => hxy j (by omega)
  have hps : prefixSum (fun i => (W i).denote (B x)) (n + 1) =
      prefixSum (fun i => (W i).denote (B y)) (n + 1) := by
    unfold prefixSum
    exact Finset.sum_congr rfl fun i hi => hw i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  rw [hw (n + 1) le_rfl, hps]

/-- **The normalized martingale converges almost surely** (on the coins whose realized weights
are `[0,1]`-valued) — **proved** (repair round 2; the T5 OPEN of record until then). For a causal
builder `B` with delay `∀ j, j < g j` and a P-generable `W`, almost surely under the i.i.d. coin
measure: if `0 ≤ (W n).denote (B x) ≤ 1` for every `n`, the normalized centred sums
`∑_{k≤N} w_k (𝟙[x k] − p) / (1 + W_k)` converge (to some limit). This is the probabilistic core
of T5 after the Kronecker reduction has been split off
(`weightedAverage_asympEq_of_normalized_tendsto`), and it is `Coin.lean`'s `nmart_tendsto_ae`
— the `L²`-bounded martingale for `Filtration.piLE`, Mathlib's
`Submartingale.ae_tendsto_limitProcess` — applied to the **clamped** realized weights
`clamp01 ((W n).denote (B x))` (the mandate's `w_n := clamp(…)`): they are `[0,1]`-valued by
construction and predictable by `weight_causal` (the day-`n` weight reads the coins `< n`, from
`CausalBuilder`, the delay and `rank_le`), and on the coins whose realized weights are
`[0,1]`-valued the clamp is the identity (`clamp01_eq_self`), so the clamped sums are the
statement's sums. The bound, not the divergence, is what the martingale argument uses
(`nweight_sq_prefixSum_le`: the telescoping `L²` step's first move `w_k² ≤ w_k`); `W_N → ∞`
enters only in the Kronecker reduction. **Without the bound the statement is false**
(`normalized_sum_unbounded_false` below — repair round 2, B1 of both audits; the round-1 form
had dropped the bound along with the divergence).
Source: [[dose-response]] §4 Prop 4.1 proof (the `L²`-martingale step); mandate T5 (3)
Kind: C
Fidelity: exact (the per-weighting martingale statement, on the `[0,1]`-weighted coins)
Hyps: (a) none -/
theorem normalized_sum_tendsto_ae (B : (ℕ → Bool) → History) (g : ℕ → ℕ) (hB : CausalBuilder B g)
    (hg : ∀ j, j < g j) (p : unitInterval) (W : ℕ → EF) (hW : PGenerableWeighting W) :
    ∀ᵐ x ∂(coinMeasure p), (∀ n, 0 ≤ (W n).denote (B x) ∧ (W n).denote (B x) ≤ 1) →
      ∃ L : ℝ, Tendsto (prefixSum (fun n =>
        (W n).denote (B x) * (truthR x n - p) /
          (1 + prefixSum (fun i => (W i).denote (B x)) n))) atTop (𝓝 L) := by
  have hc : ∀ n x y, (∀ j < n, x j = y j) →
      clamp01 ((W n).denote (B x)) = clamp01 ((W n).denote (B y)) :=
    fun n x y h => by rw [weight_causal hB hg hW n h]
  filter_upwards [nmart_tendsto_ae p (w := fun x n => clamp01 ((W n).denote (B x)))
    (fun _ _ => ⟨clamp01_nonneg _, clamp01_le_one _⟩) hc] with x hx hb
  obtain ⟨L, hL⟩ := hx
  refine ⟨L, ?_⟩
  have hcl : ∀ n, clamp01 ((W n).denote (B x)) = (W n).denote (B x) :=
    fun n => clamp01_eq_self (hb n).1 (hb n).2
  have heq : (fun N => nmart p (fun x n => clamp01 ((W n).denote (B x))) N x) =
      prefixSum (fun n => (W n).denote (B x) * (truthR x n - p) /
        (1 + prefixSum (fun i => (W i).denote (B x)) n)) := by
    funext N
    unfold nmart
    congr 1
    funext n
    simp only [nincr, hcl]
  rw [heq] at hL
  exact hL

/-- **The weighted strong law for a causal builder** (T5's step (3)). For a causal builder `B`
with delay `∀ j, j < g j` and a P-generable `W`, almost surely: if `W`'s realized mass on `B x`
diverges, the `W`-weighted truth frequency tends to `p`. **Composed** (repair round 1) from the
Kronecker reduction (`weightedAverage_asympEq_of_normalized_tendsto`, proved) and the a.s.
convergence of the normalized martingale (`normalized_sum_tendsto_ae`, proved in repair round 2;
its `[0,1]` hypothesis is `DivergentWeighting`'s first clause, `hdiv.1`). Grade (a).
Source: [[dose-response]] §4 Prop 4.1 (the martingale SLLN step); mandate T5 (3)
Kind: C
Fidelity: exact (the per-weighting form; the `[0,1]` clamp is FAF's `DivergentWeighting` bound)
Hyps: (a) none -/
theorem weighted_slln_causal (B : (ℕ → Bool) → History) (g : ℕ → ℕ) (hB : CausalBuilder B g)
    (hg : ∀ j, j < g j) (p : unitInterval) (W : ℕ → EF) (hW : PGenerableWeighting W) :
    ∀ᵐ x ∂(coinMeasure p), DivergentWeighting W (B x) →
      weightedAverage (fun i => (W i).denote (B x)) (truthR x) ≈ₙ fun _ => (p : ℝ) := by
  filter_upwards [normalized_sum_tendsto_ae B g hB hg p W hW] with x hx hdiv
  obtain ⟨L, hL⟩ := hx hdiv.1
  exact weightedAverage_asympEq_of_normalized_tendsto (fun n => (hdiv.1 n).1) hdiv.2 hL

/-! ## The `[0,1]` bound is load-bearing: the unbounded form is refuted (repair round 2) -/

/-- **The sign-alternating weighting**: `+1` on even days, `−1` on odd days — a legal
`PGenerableWeighting` (FAF's `def:ece` data carries no sign and no `[0,1]` clause), on which the
unbounded form of the OPEN fails.
Source: audit r2 B1 (both lenses; the fidelity audit's probe `NormalizedSumFalse.lean`)
Kind: D
Fidelity: n/a (a refuting instance)
Hyps: n/a -/
def altWeight (n : ℕ) : EF := EF.const (if n % 2 = 0 then 1 else -1)

/-- `altWeight` is P-generable: `fa-theorem-a`'s `evenDays_pgenerable` certificate
(`MachineSpliceStream.ifZero` on the parity ruler) with the constants `1` and `−1`.
Source: audit r2 B1; `fa-theorem-a` `evenDays_pgenerable`
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem altWeight_pgenerable : PGenerableWeighting altWeight where
  polySeg :=
    ((MachineSpliceStream.serialize_const (1 : ℚ)).ifZero
      (MachineSpliceStream.serialize_const (-1 : ℚ))
      (MachineDigits.ofUnaryRuler UnaryRuler.id).mod_two).of_eq (fun n => by
        by_cases h : n % 2 = 0
        · simp [altWeight, h]
        · simp [altWeight, h])
  rank_le := fun n => by simp [altWeight]
  closed := fun n ρ V => by simp [altWeight, EF.denote]

/-- `altWeight` denotes as `±1` by parity on every market.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem altWeight_denote (V : History) (n : ℕ) :
    (altWeight n).denote V = if n % 2 = 0 then 1 else -1 := by
  unfold altWeight
  split_ifs <;> simp

/-- The inclusive prefix sums of `altWeight` are `1` on even days and `0` on odd days, so the
normalizer `1 + W_n` is `2` or `1` — never `0`: the refutation does not go through junk division.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem altWeight_prefixSum (V : History) (n : ℕ) :
    prefixSum (fun i => (altWeight i).denote V) n = if n % 2 = 0 then 1 else 0 := by
  induction n with
  | zero => simp [prefixSum, altWeight_denote]
  | succ n ih =>
    rw [prefixSum_succ, ih, altWeight_denote]
    by_cases h : n % 2 = 0
    · have h' : ¬ (n + 1) % 2 = 0 := by omega
      simp [h, h']
    · have h' : (n + 1) % 2 = 0 := by omega
      simp [h, h']

/-- The coin probability `½` as a point of the unit interval.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def probHalf : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

/-- At `altWeight` and `p = ½` every normalized centred increment has absolute value `≥ ¼`, on
every market and every coin.
Source: audit r2 B1
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem altWeight_term_abs_ge (V : History) (x : ℕ → Bool) (n : ℕ) :
    1 / 4 ≤ |(altWeight n).denote V * (truthR x n - (probHalf : ℝ)) /
      (1 + prefixSum (fun i => (altWeight i).denote V) n)| := by
  rw [altWeight_denote, altWeight_prefixSum]
  have hξ : |truthR x n - (probHalf : ℝ)| = 1 / 2 := by
    show |truthR x n - 1 / 2| = 1 / 2
    unfold truthR
    split_ifs <;> norm_num
  rw [abs_div, abs_mul, hξ]
  split_ifs <;> norm_num

/-- For **every** coin, the normalized sums of `altWeight` at `p = ½` converge to no limit: the
increments do not tend to `0`.
Source: audit r2 B1
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem altWeight_not_tendsto (V : History) (x : ℕ → Bool) :
    ¬ ∃ L : ℝ, Tendsto (prefixSum (fun n => (altWeight n).denote V * (truthR x n - (probHalf : ℝ)) /
      (1 + prefixSum (fun i => (altWeight i).denote V) n))) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have h1 := (hL.comp (tendsto_add_atTop_nat 1)).sub hL
  rw [sub_self] at h1
  have h2 : Tendsto (fun n => (altWeight (n + 1)).denote V * (truthR x (n + 1) - (probHalf : ℝ)) /
      (1 + prefixSum (fun i => (altWeight i).denote V) (n + 1))) atTop (𝓝 0) := by
    refine h1.congr fun n => ?_
    show prefixSum _ (n + 1) - prefixSum _ n = _
    rw [prefixSum_succ]
    ring
  have h3 := h2.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨N, hN⟩ := eventually_atTop.mp h3
  have h4 := hN N le_rfl
  simp only [dist_zero_right, Real.norm_eq_abs] at h4
  linarith [altWeight_term_abs_ge V x (N + 1)]

/-- A constant builder is causal for every delay.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem causalBuilder_const (P : History) (g : ℕ → ℕ) : CausalBuilder (fun _ => P) g :=
  fun _ _ _ _ _ _ _ => rfl

/-- **N+ (the bound is load-bearing): the unbounded form of the OPEN fails for every builder.**
The round-1 statement of `normalized_sum_tendsto_ae` carried no bound on the realized weights;
at `altWeight` and `p = ½` its a.s. event is empty for *every* builder `B` (the sums converge on
no coin, `altWeight_not_tendsto`) while the coin measure is a probability measure
(`coinMeasure_ae_exists`). No `sorry` is used.
Source: audit r2 B1 (both lenses)
Kind: N+
Fidelity: exact (the refuted conclusion is the round-1 OPEN's, at a legal `PGenerableWeighting`)
Hyps: (a) none -/
theorem normalized_sum_unbounded_false (B : (ℕ → Bool) → History) :
    ¬ ∀ᵐ x ∂(coinMeasure probHalf), ∃ L : ℝ, Tendsto (prefixSum (fun n =>
      (altWeight n).denote (B x) * (truthR x n - probHalf) /
        (1 + prefixSum (fun i => (altWeight i).denote (B x)) n))) atTop (𝓝 L) := by
  intro h
  obtain ⟨x, hx⟩ := coinMeasure_ae_exists probHalf h
  exact altWeight_not_tendsto (B x) x hx

/-- **The round-1 OPEN, universally closed, is false**: refuted at the constant builder,
`g = succ`, `p = ½`, `W = altWeight` (the package's instance of record
`liaHistory (atomDP id x succ)` refutes it just the same, `normalized_sum_unbounded_false`).
Source: audit r2 B1 (both lenses)
Kind: N+
Fidelity: exact (the round-1 statement verbatim)
Hyps: (a) none -/
theorem normalized_sum_unbounded_statement_false :
    ¬ ∀ (B : (ℕ → Bool) → History) (g : ℕ → ℕ), CausalBuilder B g → (∀ j, j < g j) →
      ∀ (p : unitInterval) (W : ℕ → EF), PGenerableWeighting W →
        ∀ᵐ x ∂(coinMeasure p), ∃ L : ℝ, Tendsto (prefixSum (fun n =>
          (W n).denote (B x) * (truthR x n - p) /
            (1 + prefixSum (fun i => (W i).denote (B x)) n))) atTop (𝓝 L) := fun h =>
  normalized_sum_unbounded_false (fun _ => fun _ _ => (0 : ℝ))
    (h _ Nat.succ (causalBuilder_const _ _) (fun j => Nat.lt_succ_self j) probHalf altWeight
      altWeight_pgenerable)

/-! ## The countable intersection -/

/-- **The countable intersection (grade (a)).** If for every P-generable weighting `W` the
per-weighting law holds almost surely, then almost surely the coin inhabits FAF's
`PseudorandomFrequency` at every deferral relative to `B x`: the P-generable weightings are
`li-pseudorandom`'s explicit enumeration `genWeighting` (`genWeighting_covers`), `ae_all_iff`
over `ℕ` intersects the countably many a.s. events, and `DeferralPatient` is ignored.
Source: [[dose-response]] §4 Prop 4.1 proof ("`𝒮*` is countable … Intersect over the countable closure"); mandate T5 (4)
Kind: C
Fidelity: stronger: every deferral function at once
Hyps: (a) none -/
theorem ae_pseudorandomFrequency_of_each (B : (ℕ → Bool) → History) (p : unitInterval)
    (h : ∀ W : ℕ → EF, PGenerableWeighting W →
      ∀ᵐ x ∂(coinMeasure p), DivergentWeighting W (B x) →
        weightedAverage (fun i => (W i).denote (B x)) (truthR x) ≈ₙ fun _ => (p : ℝ)) :
    ∀ᵐ x ∂(coinMeasure p), ∀ f : DeferralFunction,
      PseudorandomFrequency (truthR x) (p : ℝ) f (B x) := by
  have h' : ∀ j : ℕ, ∀ᵐ x ∂(coinMeasure p), PGenerableWeighting (genWeighting j) →
      DivergentWeighting (genWeighting j) (B x) →
        weightedAverage (fun i => (genWeighting j i).denote (B x)) (truthR x) ≈ₙ
          fun _ => (p : ℝ) := by
    intro j
    by_cases hj : PGenerableWeighting (genWeighting j)
    · exact (h _ hj).mono fun x hx _ => hx
    · exact Filter.Eventually.of_forall fun x hj' => absurd hj' hj
  rw [← ae_all_iff] at h'
  refine h'.mono fun x hx f W hW hdiv _ => ?_
  obtain ⟨j, rfl⟩ := genWeighting_covers W hW
  exact hx j hW hdiv

/-! ## T5 — the headline, partial -/

/-- **T5, Prop 4.1 over FAF (headline; proved).** For a causal builder with delay `≥ 1` and
i.i.d. Bernoulli(`p`) coins, almost surely the realized coin inhabits FAF's `PseudorandomFrequency`
at every deferral relative to the built market — the probabilistic twin of `li-pseudorandom`'s
`pseudorandomFrequency_of_causal`. Composed from the countable intersection, the Kronecker
reduction and the a.s. convergence of the normalized martingale (`normalized_sum_tendsto_ae`,
proved in repair round 2 through `Coin.lean`'s `nmart_tendsto_ae`); grade (a) throughout, no
open input.
Source: [[dose-response]] §4 Prop 4.1; anson-049; mandate T5
Kind: C
Fidelity: stronger: every `f`; the note's "product closure" is `PGenerableWeighting.mul`
Hyps: (a) none -/
theorem randomization_justifies_tameness (B : (ℕ → Bool) → History) (g : ℕ → ℕ)
    (hB : CausalBuilder B g) (hg : ∀ j, j < g j) (p : unitInterval) :
    ∀ᵐ x ∂(coinMeasure p), ∀ f : DeferralFunction,
      PseudorandomFrequency (truthR x) (p : ℝ) f (B x) :=
  ae_pseudorandomFrequency_of_each B p fun W hW => weighted_slln_causal B g hB hg p W hW

/-- **T5 at the instance of record**: FAF's LIA over the process revealing the coin with delay
`g` (`li-pseudorandom`'s `liaHistory_atomDP_causal`) — almost surely the i.i.d. coin is
pseudorandom relative to FAF's LIA over the process that reveals it late.
Source: mandate T5 witness ("`B x := liaHistory (atomDP a x g)`")
Kind: N+ (the hypothesis package: a real causal builder, `p ∈ (0,1)` admissible; the conclusion proved, repair round 2)
Fidelity: n/a
Hyps: (a) none -/
theorem lia_atomDP_randomized (a g : ℕ → ℕ) (hg : ∀ j, j < g j) (p : unitInterval) :
    ∀ᵐ x ∂(coinMeasure p), ∀ f : DeferralFunction,
      PseudorandomFrequency (truthR x) (p : ℝ) f (liaHistory (atomDP a x g)) :=
  randomization_justifies_tameness _ g (liaHistory_atomDP_causal a g) hg p

end Cleanroom.Deference.DefDoseResponse
