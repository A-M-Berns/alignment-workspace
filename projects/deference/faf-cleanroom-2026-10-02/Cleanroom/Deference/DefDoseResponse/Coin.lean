import Cleanroom.Li.LiPseudorandom.Defs
import Cleanroom.Found.LiAsympCalc.WeightedAverage
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# `def-dose-response` · Coin: the coin measure and the probabilistic core of T5

The i.i.d. Bernoulli(`p`) coin measure `coinMeasure p` on `ℕ → Bool` (Mathlib's
`Measure.infinitePi` of `bernoulliMeasure true false p`; moved here from `Randomized.lean` in
repair round 2), and **the theorem the T5 OPEN rested on, proved**: for any weight process
`w : (ℕ → Bool) → ℕ → ℝ` that is `[0,1]`-valued and *predictable* — `w x n` depends on the coins
`x_0, …, x_{n−1}` only — the normalized centred sums

`M_N(x) := ∑_{k≤N} w x k · (𝟙[x k] − p) / (1 + W_k(x))`, `W_k(x) := ∑_{i≤k} w x i` (FAF's inclusive `prefixSum`),

converge almost surely (`nmart_tendsto_ae`). The route is the mandate's and the note's: `M` is a
martingale for Mathlib's canonical filtration `Filtration.piLE` (the σ-algebra of the coins
`≤ N` at time `N`) — its increment `w_{N+1}(𝟙[x_{N+1}] − p)/(1 + W_{N+1})` is a
`piLE N`-measurable factor times the centred coin `N + 1`, which is independent of `piLE N` under
the product measure and has mean zero (`indep_coin_piLE`, `condExp_coin_centred`,
`condExp_nincr_succ`, `martingale_nmart`); its `L²` norm is bounded by `1` through the
orthogonality of the increments (`integral_nmart_mul_nincr_succ`) and the pointwise telescoping
`∑_{k≤N} (w_k/(1+W_k))² ≤ 1 − 1/(1+W_N)` (`nweight_sq_prefixSum_le`), whose first step
`w_k² ≤ w_k` **is** the `[0,1]` bound; so Mathlib's `Submartingale.ae_tendsto_limitProcess`
applies. Everything is grade (a): Mathlib's product measure, filtration, conditional expectation
and martingale convergence theorem, FAF's `prefixSum`, `li-pseudorandom`'s `truthR`.

`Randomized.lean` applies this to the clamped realized weights `clamp01 ((W n).denote (B x))` of
a P-generable `W` on a causal builder (predictable by `weight_causal`), and on the coins whose
realized weights are `[0,1]`-valued the clamp is the identity — which is the OPEN
`normalized_sum_tendsto_ae` as restated in repair round 2, now a theorem.
-/

namespace Cleanroom.Deference.DefDoseResponse

open LogicalInduction Cleanroom.Li.LiPseudorandom Cleanroom.Found.LiAsympCalc MeasureTheory
  ProbabilityTheory
open Filter Topology
open scoped ENNReal NNReal

/-! ## The coin measure -/

/-- **The i.i.d. Bernoulli(`p`) coin measure** on `ℕ → Bool`: Mathlib's product of
`bernoulliMeasure true false p` over the days (mass `p` on `true`).
Source: [[dose-response]] §2.2 D1 ("(R) Randomized. Independent Bernoulli(`p_i`) bits"); mandate T5
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def coinMeasure (p : unitInterval) : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => bernoulliMeasure true false p

/-- The coin measure is a probability measure.
Source: none: infrastructure (Mathlib's `infinitePi` instance)
Kind: L
Fidelity: n/a -/
instance coinMeasure_isProbabilityMeasure (p : unitInterval) :
    IsProbabilityMeasure (coinMeasure p) := by
  unfold coinMeasure
  infer_instance

/-- An almost-sure statement under the coin measure has a witness: the a.s. event of T5 is not
the empty event.
Source: mandate T5 witness ("the a.s. event is not the empty event")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem coinMeasure_ae_exists (p : unitInterval) {P : (ℕ → Bool) → Prop}
    (h : ∀ᵐ x ∂(coinMeasure p), P x) : ∃ x, P x :=
  haveI : (ae (coinMeasure p)).NeBot := ae_neBot.mpr (IsProbabilityMeasure.ne_zero _)
  h.exists

/-- **The day-`n` coin has probability `p`**: the cylinder `{x_n = true}` has `coinMeasure p`-mass
`p` (`Measure.infinitePi_pi` at the one-coordinate cylinder, `bernoulliMeasure` at `{true}`).
Source: none: infrastructure (the law of one coin)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem coinMeasure_coin_true (p : unitInterval) (n : ℕ) :
    coinMeasure p {x | x n = true} = (unitInterval.toNNReal p : ℝ≥0∞) := by
  have hpi : {x : ℕ → Bool | x n = true} =
      Set.pi (↑({n} : Finset ℕ)) (fun _ => ({true} : Set Bool)) := by
    ext x
    simp
  rw [hpi]
  unfold coinMeasure
  rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _), Finset.prod_singleton,
    bernoulliMeasure_apply_of_mem_of_notMem p (measurableSet_singleton _) (Set.mem_singleton _)
      (by simp)]

/-- `truthR · n` (the coin `n` as `0`/`1`) is measurable.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem measurable_truthR (n : ℕ) : Measurable fun x : ℕ → Bool => truthR x n :=
  (measurable_of_countable (fun b : Bool => if b then (1 : ℝ) else 0)).comp (measurable_pi_apply n)

/-- `truthR · n` is integrable (bounded by `1` on a probability space).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem integrable_truthR (p : unitInterval) (n : ℕ) :
    Integrable (fun x : ℕ → Bool => truthR x n) (coinMeasure p) :=
  Integrable.of_bound (measurable_truthR n).aestronglyMeasurable 1 (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]
    unfold truthR
    split_ifs <;> norm_num)

/-- **The mean of the coin is `p`**: `∫ truthR x n ∂(coinMeasure p) = p`.
Source: none: infrastructure (the law of one coin)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem integral_truthR (p : unitInterval) (n : ℕ) :
    ∫ x, truthR x n ∂(coinMeasure p) = p := by
  have hset : MeasurableSet {x : ℕ → Bool | x n = true} := by
    show MeasurableSet ((fun x : ℕ → Bool => x n) ⁻¹' {true})
    exact measurable_pi_apply n (measurableSet_singleton true)
  have hind : (fun x : ℕ → Bool => truthR x n) = Set.indicator {x | x n = true} 1 := by
    funext x
    by_cases h : x n = true <;> simp [truthR, Set.indicator, h]
  rw [hind, integral_indicator_one hset, measureReal_def, coinMeasure_coin_true,
    ENNReal.coe_toReal, unitInterval.coe_toNNReal]

/-! ## The two probabilistic stones: independence of the next coin from the past, and the
vanishing conditional expectation of the centred coin -/

/-- **A function of the coins `≤ n` is measurable for the canonical filtration at `n`**
(Mathlib's `Filtration.piLE n`, the σ-algebra of coordinates `≤ n`): it factors through
`restrictLe n` into the finite type `Iic n → Bool`, out of which every function is measurable.
Source: none: infrastructure (the measurability stone of T5's martingale route)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem measurable_piLE_of_determined {f : (ℕ → Bool) → ℝ} (n : ℕ)
    (h : ∀ x y : ℕ → Bool, (∀ j ≤ n, x j = y j) → f x = f y) :
    Measurable[MeasureTheory.Filtration.piLE n] f := by
  classical
  let F : (Set.Iic n → Bool) → ℝ := fun z =>
    f (fun j => if hj : j ∈ Set.Iic n then z ⟨j, hj⟩ else false)
  have hF : f = fun x => F (Preorder.restrictLe n x) := by
    funext x
    show f x = f (fun j => if hj : j ∈ Set.Iic n then Preorder.restrictLe n x ⟨j, hj⟩ else false)
    apply h
    intro j hj
    rw [dif_pos (Set.mem_Iic.mpr hj)]
    rfl
  have hpi : (MeasureTheory.Filtration.piLE n : MeasurableSpace (ℕ → Bool)) =
      MeasurableSpace.pi.comap (Preorder.restrictLe n) := rfl
  rw [hF, hpi]
  exact (measurable_of_countable F).comp
    (comap_measurable (m := MeasurableSpace.pi) (Preorder.restrictLe (π := fun _ => Bool) n))

/-- **The coin `n + 1` is independent of the coins `≤ n`** under the product measure: the
σ-algebra generated by coordinate `n + 1` is independent of `Filtration.piLE n` (Mathlib's
`iIndepFun_infinitePi`, the finset form `iIndepFun.indepFun_finset` at `{n+1}` and
`range (n+1)`, composed with the evaluation and the restriction to `Iic n`).
Source: [[dose-response]] §4 Prop 4.1 proof ("`ξ_n` is independent of `𝓕_{n−1}`"); mandate T5 (3)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem indep_coin_piLE (p : unitInterval) (n : ℕ) :
    Indep (MeasurableSpace.comap (fun x : ℕ → Bool => x (n + 1)) ⊤)
      (MeasureTheory.Filtration.piLE n) (coinMeasure p) := by
  have hI : iIndepFun (fun (i : ℕ) (x : ℕ → Bool) => x i) (coinMeasure p) := by
    unfold coinMeasure
    exact iIndepFun_infinitePi (X := fun _ : ℕ => (id : Bool → Bool)) (fun _ => measurable_id)
  have h1 := hI.indepFun_finset {n + 1} (Finset.range (n + 1))
    (Finset.disjoint_singleton_left.mpr (by simp)) (fun i => measurable_pi_apply i)
  have h2 := h1.comp
    (φ := fun z : (({n + 1} : Finset ℕ) : Type) → Bool => z ⟨n + 1, Finset.mem_singleton_self _⟩)
    (ψ := fun z : ((Finset.range (n + 1) : Finset ℕ) : Type) → Bool =>
      fun i : Set.Iic n => z ⟨i.1, Finset.mem_range.mpr (Nat.lt_succ_of_le i.2)⟩)
    (measurable_pi_apply (X := fun _ : (({n + 1} : Finset ℕ) : Type) => Bool)
      ⟨n + 1, Finset.mem_singleton_self _⟩)
    (measurable_pi_lambda _ fun i =>
      measurable_pi_apply (X := fun _ : ((Finset.range (n + 1) : Finset ℕ) : Type) => Bool)
        ⟨i.1, Finset.mem_range.mpr (Nat.lt_succ_of_le i.2)⟩)
  exact h2

/-- **The centred coin `n + 1` has conditional expectation `0` given the coins `≤ n`**:
`𝔼[𝟙[x_{n+1}] − p | piLE n] = 0` a.s. (Mathlib's `condExp_indep_eq` at `indep_coin_piLE`, and
the mean `integral_truthR`).
Source: [[dose-response]] §4 Prop 4.1 proof ("`𝔼[ξ_n | 𝓕_{n−1}] = 0`"); mandate T5 (3)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem condExp_coin_centred (p : unitInterval) (n : ℕ) :
    (coinMeasure p)[fun x => truthR x (n + 1) - (p : ℝ) | MeasureTheory.Filtration.piLE n]
      =ᵐ[coinMeasure p] fun _ => (0 : ℝ) := by
  have hle₁ : MeasurableSpace.comap (fun x : ℕ → Bool => x (n + 1)) ⊤ ≤ MeasurableSpace.pi :=
    measurable_iff_comap_le.mp (measurable_pi_apply (n + 1))
  have hmeas : StronglyMeasurable[MeasurableSpace.comap (fun x : ℕ → Bool => x (n + 1)) ⊤]
      (fun x => truthR x (n + 1) - (p : ℝ)) :=
    ((measurable_of_countable (fun b : Bool => (if b then (1 : ℝ) else 0) - p)).comp
      (comap_measurable _)).stronglyMeasurable
  refine (condExp_indep_eq hle₁ ((MeasureTheory.Filtration.piLE (X := fun _ : ℕ => Bool)).le n)
    hmeas (indep_coin_piLE p n)).trans (Filter.Eventually.of_forall fun _ => ?_)
  show ∫ x, (truthR x (n + 1) - (p : ℝ)) ∂(coinMeasure p) = 0
  rw [integral_sub (integrable_truthR p (n + 1)) (integrable_const _), integral_truthR,
    integral_const]
  simp

/-! ## The normalized martingale of a predictable `[0,1]` weight process -/

section Core

variable (p : unitInterval) (w : (ℕ → Bool) → ℕ → ℝ)

/-- **The normalized weight** `w_n/(1 + W_n)`, `W_n := ∑_{i≤n} w_i` (FAF's inclusive `prefixSum`),
of a weight process `w` on the coin space.
Source: [[dose-response]] §4 Prop 4.1 proof; mandate T5 (3)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def nweight (x : ℕ → Bool) (n : ℕ) : ℝ := w x n / (1 + prefixSum (w x) n)

/-- **The normalized centred increment** `w_n (𝟙[x_n] − p)/(1 + W_n)` — the summand of the OPEN
`normalized_sum_tendsto_ae`, verbatim.
Source: [[dose-response]] §4 Prop 4.1 proof; mandate T5 (3)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def nincr (x : ℕ → Bool) (n : ℕ) : ℝ :=
  w x n * (truthR x n - p) / (1 + prefixSum (w x) n)

/-- **The normalized martingale** `M_N := ∑_{k≤N} w_k (𝟙[x_k] − p)/(1 + W_k)`, as a process
indexed by the day (the OPEN's `prefixSum`, with the day first).
Source: [[dose-response]] §4 Prop 4.1 proof ("`M_N` is a martingale"); mandate T5 (3)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def nmart (N : ℕ) (x : ℕ → Bool) : ℝ := prefixSum (nincr p w x) N

variable {w}

/-- The increment factors as the normalized weight times the centred coin.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem nincr_eq (x : ℕ → Bool) (n : ℕ) :
    nincr p w x n = nweight w x n * (truthR x n - p) := by
  unfold nincr nweight
  rw [mul_div_right_comm]

/-- `M_{N+1} = M_N + ` the increment `N + 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem nmart_succ (N : ℕ) :
    nmart p w (N + 1) = nmart p w N + fun x => nincr p w x (N + 1) := by
  funext x
  simp only [nmart, Pi.add_apply]
  exact prefixSum_succ _ _

/-- `M_0` is the increment `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem nmart_zero : nmart p w 0 = fun x => nincr p w x 0 := by
  funext x
  simp [nmart, prefixSum]

/-- The centred coin is bounded by `1` in absolute value.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem abs_centred_le (x : ℕ → Bool) (n : ℕ) : |truthR x n - (p : ℝ)| ≤ 1 := by
  have h0 : (0 : ℝ) ≤ p := p.2.1
  have h1 : (p : ℝ) ≤ 1 := p.2.2
  unfold truthR
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

/-- The centred coin is measurable.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem measurable_centred (n : ℕ) : Measurable fun x : ℕ → Bool => truthR x n - (p : ℝ) :=
  (measurable_truthR n).sub measurable_const

/-- The centred coin is integrable.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem integrable_centred (n : ℕ) :
    Integrable (fun x : ℕ → Bool => truthR x n - (p : ℝ)) (coinMeasure p) :=
  (integrable_truthR p n).sub (integrable_const _)

/-- A bounded measurable function is integrable for the coin measure.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem integrable_of_abs_le {f : (ℕ → Bool) → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) : Integrable f (coinMeasure p) :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]
    exact hC x)

/-! ### Bounds, for a `[0,1]`-valued weight process -/

/-- The prefix sums of a nonnegative weight process are nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem prefixSum_w_nonneg (hw : ∀ x n, 0 ≤ w x n ∧ w x n ≤ 1) (x : ℕ → Bool) (n : ℕ) :
    0 ≤ prefixSum (w x) n :=
  prefixSum_nonneg (fun i => (hw x i).1) n

/-- The normalizer `1 + W_n` is positive — no junk division anywhere in the martingale.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem one_add_prefixSum_pos (hw : ∀ x n, 0 ≤ w x n ∧ w x n ≤ 1) (x : ℕ → Bool) (n : ℕ) :
    0 < 1 + prefixSum (w x) n := by
  have := prefixSum_w_nonneg hw x n
  linarith

/-- The normalized weight is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem nweight_nonneg (hw : ∀ x n, 0 ≤ w x n ∧ w x n ≤ 1) (x : ℕ → Bool) (n : ℕ) :
    0 ≤ nweight w x n :=
  div_nonneg (hw x n).1 (one_add_prefixSum_pos hw x n).le

/-- The normalized weight is at most `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem nweight_le_one (hw : ∀ x n, 0 ≤ w x n ∧ w x n ≤ 1) (x : ℕ → Bool) (n : ℕ) :
    nweight w x n ≤ 1 := by
  unfold nweight
  rw [div_le_one (one_add_prefixSum_pos hw x n)]
  have := prefixSum_w_nonneg hw x n
  linarith [(hw x n).2]

/-- The increment is bounded by `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem abs_nincr_le (hw : ∀ x n, 0 ≤ w x n ∧ w x n ≤ 1) (x : ℕ → Bool) (n : ℕ) :
    |nincr p w x n| ≤ 1 := by
  rw [nincr_eq, abs_mul, abs_of_nonneg (nweight_nonneg hw x n)]
  calc nweight w x n * |truthR x n - (p : ℝ)| ≤ 1 * 1 :=
        mul_le_mul (nweight_le_one hw x n) (abs_centred_le p x n) (abs_nonneg _) zero_le_one
    _ = 1 := by ring

/-- `M_N` is bounded by `N + 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem abs_nmart_le (hw : ∀ x n, 0 ≤ w x n ∧ w x n ≤ 1) (N : ℕ) (x : ℕ → Bool) :
    |nmart p w N x| ≤ N + 1 := by
  unfold nmart prefixSum
  calc |∑ i ∈ Finset.range (N + 1), nincr p w x i|
      ≤ ∑ i ∈ Finset.range (N + 1), |nincr p w x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (N + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => abs_nincr_le p hw x i
    _ = N + 1 := by simp

/-- **The telescoping bound**: `∑_{k≤n} (w_k/(1+W_k))² + 1/(1+W_n) ≤ 1`, by induction on `n`,
through `w_k²/(1+W_k)² ≤ w_k/((1+W_{k−1})(1+W_k)) = 1/(1+W_{k−1}) − 1/(1+W_k)` — whose first step
`w_k² ≤ w_k` is exactly the `[0,1]` bound (the step that fails for the round-1 unbounded form).
Source: [[dose-response]] §4 Prop 4.1 proof ("`∑ 𝔼[Δ_k²] ≤ ∑ w_k²/(1+W_k)² ≤ 1`"); mandate T5 (3)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem nweight_sq_prefixSum_le (hw : ∀ x n, 0 ≤ w x n ∧ w x n ≤ 1) (x : ℕ → Bool) (n : ℕ) :
    prefixSum (fun k => nweight w x k ^ 2) n + 1 / (1 + prefixSum (w x) n) ≤ 1 := by
  induction n with
  | zero =>
    simp only [prefixSum, zero_add, Finset.sum_range_one, nweight]
    have h0 := (hw x 0).1
    have hpos : (0 : ℝ) < 1 + w x 0 := by linarith
    rw [div_pow, div_add_div _ _ (pow_ne_zero 2 hpos.ne') hpos.ne', div_le_one (by positivity)]
    nlinarith [sq_nonneg (w x 0)]
  | succ n ih =>
    rw [prefixSum_succ, prefixSum_succ]
    have hW := prefixSum_w_nonneg hw x n
    have h0 := (hw x (n + 1)).1
    have h1 := (hw x (n + 1)).2
    have hkey : nweight w x (n + 1) ^ 2 + 1 / (1 + (prefixSum (w x) n + w x (n + 1))) ≤
        1 / (1 + prefixSum (w x) n) := by
      unfold nweight
      rw [prefixSum_succ]
      have ha : (0 : ℝ) < 1 + prefixSum (w x) n := by linarith
      have hs : (0 : ℝ) < 1 + (prefixSum (w x) n + w x (n + 1)) := by linarith
      have hb2 : w x (n + 1) ^ 2 ≤ w x (n + 1) := by nlinarith
      have hab : prefixSum (w x) n * w x (n + 1) ^ 2 ≤ prefixSum (w x) n * w x (n + 1) :=
        mul_le_mul_of_nonneg_left hb2 hW
      have hcore : (w x (n + 1) ^ 2 + (1 + (prefixSum (w x) n + w x (n + 1)))) *
          (1 + prefixSum (w x) n) ≤ (1 + (prefixSum (w x) n + w x (n + 1))) ^ 2 := by
        nlinarith
      rw [div_pow, div_add_div _ _ (pow_ne_zero 2 hs.ne') hs.ne', div_le_div_iff₀ (by positivity) ha]
      nlinarith [mul_le_mul_of_nonneg_left hcore hs.le]
    linarith

/-- The telescoping bound without its tail: `∑_{k≤n} (w_k/(1+W_k))² ≤ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem nweight_sq_prefixSum_le_one (hw : ∀ x n, 0 ≤ w x n ∧ w x n ≤ 1) (x : ℕ → Bool) (n : ℕ) :
    prefixSum (fun k => nweight w x k ^ 2) n ≤ 1 := by
  have h := nweight_sq_prefixSum_le hw x n
  have : 0 ≤ 1 / (1 + prefixSum (w x) n) := by
    have := one_add_prefixSum_pos hw x n
    positivity
  linarith

/-! ### Predictability: `w_n` reads the coins `< n`, so `M_N` reads the coins `≤ N` -/

/-- The prefix sums of a predictable weight process are determined by the coins `< n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem prefixSum_w_determined (hc : ∀ n x y, (∀ j < n, x j = y j) → w x n = w y n) (n : ℕ)
    {x y : ℕ → Bool} (h : ∀ j < n, x j = y j) : prefixSum (w x) n = prefixSum (w y) n := by
  unfold prefixSum
  refine Finset.sum_congr rfl fun i hi => hc i x y fun j hj => h j ?_
  exact lt_of_lt_of_le hj (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-- The normalized weight is determined by the coins `< n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem nweight_determined (hc : ∀ n x y, (∀ j < n, x j = y j) → w x n = w y n) (n : ℕ)
    {x y : ℕ → Bool} (h : ∀ j < n, x j = y j) : nweight w x n = nweight w y n := by
  unfold nweight
  rw [hc n x y h, prefixSum_w_determined hc n h]

/-- The increment is determined by the coins `≤ n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem nincr_determined (hc : ∀ n x y, (∀ j < n, x j = y j) → w x n = w y n) (n : ℕ)
    {x y : ℕ → Bool} (h : ∀ j ≤ n, x j = y j) : nincr p w x n = nincr p w y n := by
  have h' : ∀ j < n, x j = y j := fun j hj => h j hj.le
  unfold nincr
  rw [hc n x y h', prefixSum_w_determined hc n h']
  unfold truthR
  rw [h n le_rfl]

/-- `M_N` is determined by the coins `≤ N`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem nmart_determined (hc : ∀ n x y, (∀ j < n, x j = y j) → w x n = w y n) (N : ℕ)
    {x y : ℕ → Bool} (h : ∀ j ≤ N, x j = y j) : nmart p w N x = nmart p w N y := by
  unfold nmart prefixSum
  refine Finset.sum_congr rfl fun i hi => nincr_determined p hc i fun j hj => h j ?_
  exact le_trans hj (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-- **`M` is adapted**: `M_N` is `piLE N`-measurable.
Source: [[dose-response]] §4 Prop 4.1 proof; mandate T5 (3)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem measurable_nmart (hc : ∀ n x y, (∀ j < n, x j = y j) → w x n = w y n) (N : ℕ) :
    Measurable[MeasureTheory.Filtration.piLE N] (nmart p w N) :=
  measurable_piLE_of_determined N fun _ _ h => nmart_determined p hc N h

/-- **The increment factor is predictable**: `w_{n+1}/(1 + W_{n+1})` is `piLE n`-measurable.
Source: [[dose-response]] §4 Prop 4.1 proof ("`w_n` is `𝓕_{n−1}`-measurable"); mandate T5 (3)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem measurable_nweight_succ (hc : ∀ n x y, (∀ j < n, x j = y j) → w x n = w y n) (n : ℕ) :
    Measurable[MeasureTheory.Filtration.piLE n] (fun x => nweight w x (n + 1)) :=
  measurable_piLE_of_determined n fun _ _ h =>
    nweight_determined hc (n + 1) fun j hj => h j (Nat.lt_succ_iff.mp hj)

/-- The normalized weight at `n` is `piLE n`-measurable (it reads the coins `< n`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem measurable_nweight (hc : ∀ n x y, (∀ j < n, x j = y j) → w x n = w y n) (n : ℕ) :
    Measurable[MeasureTheory.Filtration.piLE n] (fun x => nweight w x n) :=
  measurable_piLE_of_determined n fun _ _ h => nweight_determined hc n fun j hj => h j hj.le

/-- The increment at `n` is `piLE n`-measurable.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem measurable_nincr (hc : ∀ n x y, (∀ j < n, x j = y j) → w x n = w y n) (n : ℕ) :
    Measurable[MeasureTheory.Filtration.piLE n] (fun x => nincr p w x n) :=
  measurable_piLE_of_determined n fun _ _ h => nincr_determined p hc n h

/-- `M_N` is measurable for the product σ-algebra.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem measurable_nmart' (hc : ∀ n x y, (∀ j < n, x j = y j) → w x n = w y n) (N : ℕ) :
    Measurable (nmart p w N) :=
  (measurable_nmart p hc N).mono ((MeasureTheory.Filtration.piLE (X := fun _ : ℕ => Bool)).le N)
    le_rfl

/-- The normalized weight is measurable for the product σ-algebra.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem measurable_nweight' (hc : ∀ n x y, (∀ j < n, x j = y j) → w x n = w y n) (n : ℕ) :
    Measurable (fun x => nweight w x n) :=
  (measurable_nweight hc n).mono ((MeasureTheory.Filtration.piLE (X := fun _ : ℕ => Bool)).le n)
    le_rfl

/-- The increment is measurable for the product σ-algebra.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem measurable_nincr' (hc : ∀ n x y, (∀ j < n, x j = y j) → w x n = w y n) (n : ℕ) :
    Measurable (fun x => nincr p w x n) :=
  (measurable_nincr p hc n).mono ((MeasureTheory.Filtration.piLE (X := fun _ : ℕ => Bool)).le n)
    le_rfl

/-- `M_N` is integrable.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem integrable_nmart (hw : ∀ x n, 0 ≤ w x n ∧ w x n ≤ 1)
    (hc : ∀ n x y, (∀ j < n, x j = y j) → w x n = w y n) (N : ℕ) :
    Integrable (nmart p w N) (coinMeasure p) :=
  integrable_of_abs_le p (measurable_nmart' p hc N) (N + 1) (abs_nmart_le p hw N)

/-- The increment is integrable.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem integrable_nincr (hw : ∀ x n, 0 ≤ w x n ∧ w x n ≤ 1)
    (hc : ∀ n x y, (∀ j < n, x j = y j) → w x n = w y n) (n : ℕ) :
    Integrable (fun x => nincr p w x n) (coinMeasure p) :=
  integrable_of_abs_le p (measurable_nincr' p hc n) 1 fun x => abs_nincr_le p hw x n

/-! ### The martingale property -/

/-- **The conditional expectation of the increment `n + 1` given the coins `≤ n` vanishes**:
the pull-out property on the predictable factor (`condExp_mul_of_stronglyMeasurable_left`) and
the centred coin's conditional expectation `condExp_coin_centred`.
Source: [[dose-response]] §4 Prop 4.1 proof ("`𝔼[Δ_{n+1} | 𝓕_n] = w_{n+1}/(1+W_{n+1}) · 𝔼[ξ_{n+1} | 𝓕_n] = 0`"); mandate T5 (3)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem condExp_nincr_succ (hw : ∀ x n, 0 ≤ w x n ∧ w x n ≤ 1)
    (hc : ∀ n x y, (∀ j < n, x j = y j) → w x n = w y n) (n : ℕ) :
    (coinMeasure p)[fun x => nincr p w x (n + 1) | MeasureTheory.Filtration.piLE n]
      =ᵐ[coinMeasure p] fun _ => (0 : ℝ) := by
  have hfun : (fun x => nincr p w x (n + 1)) =
      (fun x => nweight w x (n + 1)) * (fun x => truthR x (n + 1) - (p : ℝ)) := by
    funext x
    simp only [Pi.mul_apply, nincr_eq]
  have hint : Integrable ((fun x => nweight w x (n + 1)) * (fun x => truthR x (n + 1) - (p : ℝ)))
      (coinMeasure p) := by
    rw [← hfun]
    exact integrable_nincr p hw hc (n + 1)
  rw [hfun]
  refine (condExp_mul_of_stronglyMeasurable_left (measurable_nweight_succ hc n).stronglyMeasurable
    hint (integrable_centred p (n + 1))).trans ?_
  filter_upwards [condExp_coin_centred p n] with x hx
  simp [hx]

/-- **`M` is a martingale for the canonical filtration** (Mathlib's `martingale_nat`: adapted,
integrable, and `𝔼[M_{N+1} | piLE N] = M_N` from `condExp_nincr_succ`).
Source: [[dose-response]] §4 Prop 4.1 proof ("`M_N` is a martingale"); mandate T5 (3)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem martingale_nmart (hw : ∀ x n, 0 ≤ w x n ∧ w x n ≤ 1)
    (hc : ∀ n x y, (∀ j < n, x j = y j) → w x n = w y n) :
    Martingale (nmart p w) (MeasureTheory.Filtration.piLE) (coinMeasure p) := by
  refine martingale_nat (fun N => (measurable_nmart p hc N).stronglyMeasurable)
    (fun N => integrable_nmart p hw hc N) fun N => ?_
  rw [nmart_succ]
  have h1 := condExp_add (μ := coinMeasure p) (integrable_nmart p hw hc N)
    (integrable_nincr p hw hc (N + 1)) (MeasureTheory.Filtration.piLE N)
  rw [condExp_of_stronglyMeasurable ((MeasureTheory.Filtration.piLE (X := fun _ : ℕ => Bool)).le N)
    (measurable_nmart p hc N).stronglyMeasurable (integrable_nmart p hw hc N)] at h1
  refine (h1.trans ?_).symm
  filter_upwards [condExp_nincr_succ p hw hc N] with x hx
  simp [hx]

/-! ### The `L²` bound -/

/-- **Orthogonality of the increments**: `𝔼[M_N · Δ_{N+1}] = 0` — through the conditional
expectation given `piLE N` (`integral_condExp`, the pull-out property on the `piLE N`-measurable
factor `M_N · w_{N+1}/(1+W_{N+1})`, and `condExp_coin_centred`).
Source: [[dose-response]] §4 Prop 4.1 proof (the `L²` bound: orthogonality of martingale increments); mandate T5 (3)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem integral_nmart_mul_nincr_succ (hw : ∀ x n, 0 ≤ w x n ∧ w x n ≤ 1)
    (hc : ∀ n x y, (∀ j < n, x j = y j) → w x n = w y n) (N : ℕ) :
    ∫ x, nmart p w N x * nincr p w x (N + 1) ∂(coinMeasure p) = 0 := by
  have hfun : (fun x => nmart p w N x * nincr p w x (N + 1)) =
      (fun x => nmart p w N x * nweight w x (N + 1)) *
        (fun x => truthR x (N + 1) - (p : ℝ)) := by
    funext x
    simp only [Pi.mul_apply, nincr_eq]
    ring
  have hg : StronglyMeasurable[MeasureTheory.Filtration.piLE N]
      (fun x => nmart p w N x * nweight w x (N + 1)) :=
    ((measurable_nmart p hc N).mul (measurable_nweight_succ hc N)).stronglyMeasurable
  have hint : Integrable ((fun x => nmart p w N x * nweight w x (N + 1)) *
      (fun x => truthR x (N + 1) - (p : ℝ))) (coinMeasure p) := by
    rw [← hfun]
    refine integrable_of_abs_le p ((measurable_nmart' p hc N).mul (measurable_nincr' p hc (N + 1)))
      ((N : ℝ) + 1) fun x => ?_
    rw [abs_mul]
    calc |nmart p w N x| * |nincr p w x (N + 1)| ≤ (N + 1) * 1 :=
          mul_le_mul (abs_nmart_le p hw N x) (abs_nincr_le p hw x (N + 1)) (abs_nonneg _)
            (by positivity)
      _ = N + 1 := by ring
  have key : ∫ x, ((fun x => nmart p w N x * nweight w x (N + 1)) *
      (fun x => truthR x (N + 1) - (p : ℝ))) x ∂(coinMeasure p) = 0 := by
    rw [← integral_condExp ((MeasureTheory.Filtration.piLE (X := fun _ : ℕ => Bool)).le N),
      integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hg hint
        (integrable_centred p (N + 1)))]
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [condExp_coin_centred p N] with x hx
    simp [hx]
  rw [hfun]
  exact key

/-- The square of `M_N` is integrable.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem integrable_nmart_sq (hw : ∀ x n, 0 ≤ w x n ∧ w x n ≤ 1)
    (hc : ∀ n x y, (∀ j < n, x j = y j) → w x n = w y n) (N : ℕ) :
    Integrable (fun x => nmart p w N x ^ 2) (coinMeasure p) :=
  integrable_of_abs_le p ((measurable_nmart' p hc N).pow_const 2) ((N + 1) ^ 2) fun x => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_nmart_le p hw N x) 2

/-- The square of the normalized weight is integrable.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem integrable_nweight_sq (hw : ∀ x n, 0 ≤ w x n ∧ w x n ≤ 1)
    (hc : ∀ n x y, (∀ j < n, x j = y j) → w x n = w y n) (n : ℕ) :
    Integrable (fun x => nweight w x n ^ 2) (coinMeasure p) :=
  integrable_of_abs_le p ((measurable_nweight' hc n).pow_const 2) 1 fun x => by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (nweight_nonneg hw x n) (nweight_le_one hw x n)

/-- The prefix sums of the squared normalized weights are integrable.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem integrable_nweightSq_prefixSum (hw : ∀ x n, 0 ≤ w x n ∧ w x n ≤ 1)
    (hc : ∀ n x y, (∀ j < n, x j = y j) → w x n = w y n) (N : ℕ) :
    Integrable (fun x => prefixSum (fun k => nweight w x k ^ 2) N) (coinMeasure p) := by
  have hmeas : Measurable fun x => prefixSum (fun k => nweight w x k ^ 2) N := by
    unfold prefixSum
    exact Finset.measurable_sum _ fun k _ => (measurable_nweight' hc k).pow_const 2
  refine integrable_of_abs_le p hmeas 1 fun x => ?_
  rw [abs_of_nonneg (prefixSum_nonneg (fun k => sq_nonneg _) N)]
  exact nweight_sq_prefixSum_le_one hw x N

/-- The squared increment is bounded by the squared normalized weight.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem nincr_sq_le (x : ℕ → Bool) (n : ℕ) : nincr p w x n ^ 2 ≤ nweight w x n ^ 2 := by
  rw [nincr_eq, mul_pow]
  have h := abs_le.mp (abs_centred_le p x n)
  have hsq : (truthR x n - (p : ℝ)) ^ 2 ≤ 1 := by nlinarith [h.1, h.2]
  exact mul_le_of_le_one_right (sq_nonneg _) hsq

/-- **The second moment of `M_N` is bounded by the telescoping sum**:
`𝔼[M_N²] ≤ 𝔼[∑_{k≤N} (w_k/(1+W_k))²]`, by induction on `N` through the orthogonality
`integral_nmart_mul_nincr_succ` and `Δ_k² ≤ (w_k/(1+W_k))²`.
Source: [[dose-response]] §4 Prop 4.1 proof (the `L²` bound); mandate T5 (3)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem integral_nmart_sq_le (hw : ∀ x n, 0 ≤ w x n ∧ w x n ≤ 1)
    (hc : ∀ n x y, (∀ j < n, x j = y j) → w x n = w y n) (N : ℕ) :
    ∫ x, nmart p w N x ^ 2 ∂(coinMeasure p) ≤
      ∫ x, prefixSum (fun k => nweight w x k ^ 2) N ∂(coinMeasure p) := by
  induction N with
  | zero =>
    refine integral_mono (integrable_nmart_sq p hw hc 0) (integrable_nweightSq_prefixSum p hw hc 0)
      fun x => ?_
    show nmart p w 0 x ^ 2 ≤ prefixSum (fun k => nweight w x k ^ 2) 0
    rw [nmart_zero]
    simp only [prefixSum, zero_add, Finset.sum_range_one]
    exact nincr_sq_le p x 0
  | succ N ih =>
    have hsplit : ∀ x, nmart p w (N + 1) x ^ 2 =
        nmart p w N x ^ 2 + 2 * (nmart p w N x * nincr p w x (N + 1)) +
          nincr p w x (N + 1) ^ 2 := fun x => by
      rw [nmart_succ]
      simp only [Pi.add_apply]
      ring
    have hint1 := integrable_nmart_sq p hw hc N
    have hint2 : Integrable (fun x => nmart p w N x * nincr p w x (N + 1)) (coinMeasure p) := by
      refine integrable_of_abs_le p
        ((measurable_nmart' p hc N).mul (measurable_nincr' p hc (N + 1))) ((N : ℝ) + 1)
        fun x => ?_
      rw [abs_mul]
      calc |nmart p w N x| * |nincr p w x (N + 1)| ≤ (N + 1) * 1 :=
            mul_le_mul (abs_nmart_le p hw N x) (abs_nincr_le p hw x (N + 1)) (abs_nonneg _)
              (by positivity)
        _ = N + 1 := by ring
    have hint3 : Integrable (fun x => nincr p w x (N + 1) ^ 2) (coinMeasure p) :=
      integrable_of_abs_le p ((measurable_nincr' p hc (N + 1)).pow_const 2) 1 fun x => by
        rw [abs_pow]
        exact pow_le_one₀ (abs_nonneg _) (abs_nincr_le p hw x (N + 1))
    have hint4 := integrable_nweightSq_prefixSum p hw hc N
    have hint5 := integrable_nweight_sq p hw hc (N + 1)
    have hint2' : Integrable (fun x => 2 * (nmart p w N x * nincr p w x (N + 1)))
        (coinMeasure p) := hint2.const_mul 2
    have hint12 : Integrable (fun x => nmart p w N x ^ 2 +
        2 * (nmart p w N x * nincr p w x (N + 1))) (coinMeasure p) := hint1.add hint2'
    calc ∫ x, nmart p w (N + 1) x ^ 2 ∂(coinMeasure p)
        = ∫ x, (nmart p w N x ^ 2 + 2 * (nmart p w N x * nincr p w x (N + 1)) +
            nincr p w x (N + 1) ^ 2) ∂(coinMeasure p) := by simp only [hsplit]
      _ = ∫ x, nmart p w N x ^ 2 ∂(coinMeasure p) +
            2 * ∫ x, nmart p w N x * nincr p w x (N + 1) ∂(coinMeasure p) +
            ∫ x, nincr p w x (N + 1) ^ 2 ∂(coinMeasure p) := by
          rw [integral_add hint12 hint3, integral_add hint1 hint2', integral_const_mul]
      _ = ∫ x, nmart p w N x ^ 2 ∂(coinMeasure p) +
            ∫ x, nincr p w x (N + 1) ^ 2 ∂(coinMeasure p) := by
          rw [integral_nmart_mul_nincr_succ p hw hc N, mul_zero, add_zero]
      _ ≤ ∫ x, prefixSum (fun k => nweight w x k ^ 2) N ∂(coinMeasure p) +
            ∫ x, nweight w x (N + 1) ^ 2 ∂(coinMeasure p) :=
          add_le_add ih (integral_mono hint3 hint5 fun x => nincr_sq_le p x (N + 1))
      _ = ∫ x, prefixSum (fun k => nweight w x k ^ 2) (N + 1) ∂(coinMeasure p) := by
          rw [← integral_add hint4 hint5]
          congr 1
          funext x
          exact (prefixSum_succ _ _).symm

/-- **`𝔼[M_N²] ≤ 1`** for every `N`: the telescoping bound integrated.
Source: [[dose-response]] §4 Prop 4.1 proof ("`sup_N 𝔼[M_N²] ≤ 1`"); mandate T5 (3)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem integral_nmart_sq_le_one (hw : ∀ x n, 0 ≤ w x n ∧ w x n ≤ 1)
    (hc : ∀ n x y, (∀ j < n, x j = y j) → w x n = w y n) (N : ℕ) :
    ∫ x, nmart p w N x ^ 2 ∂(coinMeasure p) ≤ 1 := by
  refine (integral_nmart_sq_le p hw hc N).trans ?_
  calc ∫ x, prefixSum (fun k => nweight w x k ^ 2) N ∂(coinMeasure p)
      ≤ ∫ _x, (1 : ℝ) ∂(coinMeasure p) :=
        integral_mono (integrable_nweightSq_prefixSum p hw hc N) (integrable_const _)
          fun x => nweight_sq_prefixSum_le_one hw x N
    _ = 1 := by simp

/-- **`M` is bounded in `L¹`** (by `1`): `L¹ ≤ L²` on a probability space, and `𝔼[M_N²] ≤ 1`.
Source: [[dose-response]] §4 Prop 4.1 proof; mandate T5 (3)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem eLpNorm_nmart_le_one (hw : ∀ x n, 0 ≤ w x n ∧ w x n ≤ 1)
    (hc : ∀ n x y, (∀ j < n, x j = y j) → w x n = w y n) (N : ℕ) :
    eLpNorm (nmart p w N) 1 (coinMeasure p) ≤ 1 := by
  have hmeas : AEStronglyMeasurable (nmart p w N) (coinMeasure p) :=
    (measurable_nmart' p hc N).aestronglyMeasurable
  refine (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2) hmeas).trans ?_
  have hmem : MemLp (nmart p w N) 2 (coinMeasure p) :=
    MemLp.of_bound hmeas ((N : ℝ) + 1) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact abs_nmart_le p hw N x)
  rw [hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, ENNReal.ofReal_le_one]
  simp only [ENNReal.toReal_ofNat]
  refine Real.rpow_le_one (integral_nonneg fun x => by positivity) ?_ (by norm_num)
  calc ∫ x, ‖nmart p w N x‖ ^ (2 : ℝ) ∂(coinMeasure p)
      = ∫ x, nmart p w N x ^ 2 ∂(coinMeasure p) := by
        congr 1
        funext x
        rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
    _ ≤ 1 := integral_nmart_sq_le_one p hw hc N

/-! ### The theorem -/

/-- **The normalized martingale converges almost surely** (the probabilistic core of T5, proved):
for any `[0,1]`-valued predictable weight process `w` on the coin space, almost surely under the
i.i.d. Bernoulli(`p`) coin measure the normalized centred sums
`M_N = ∑_{k≤N} w_k (𝟙[x_k] − p)/(1 + W_k)` converge to some limit — Mathlib's
`Submartingale.ae_tendsto_limitProcess` on the `L¹`-bounded martingale `martingale_nmart`.
Source: [[dose-response]] §4 Prop 4.1 proof (the `L²`-martingale step); mandate T5 (3)
Kind: C
Fidelity: exact (the martingale statement, for every predictable `[0,1]` weight process)
Hyps: (a) none -/
theorem nmart_tendsto_ae (hw : ∀ x n, 0 ≤ w x n ∧ w x n ≤ 1)
    (hc : ∀ n x y, (∀ j < n, x j = y j) → w x n = w y n) :
    ∀ᵐ x ∂(coinMeasure p), ∃ L : ℝ, Tendsto (fun N => nmart p w N x) atTop (𝓝 L) := by
  have hb : ∀ N, eLpNorm (nmart p w N) 1 (coinMeasure p) ≤ ((1 : ℝ≥0) : ℝ≥0∞) := fun N => by
    rw [ENNReal.coe_one]
    exact eLpNorm_nmart_le_one p hw hc N
  filter_upwards [(martingale_nmart p hw hc).submartingale.ae_tendsto_limitProcess hb] with x hx
  exact ⟨_, hx⟩

end Core

/-! ## The clamp to `[0,1]` -/

/-- **The clamp** `min 1 (max 0 t)` — the mandate's `w_n := clamp ((W n).denote (B x))`.
Source: mandate T5 (3) ("`w_n := clamp ((W n).denote (B x))`")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def clamp01 (t : ℝ) : ℝ := min 1 (max 0 t)

/-- The clamp is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem clamp01_nonneg (t : ℝ) : 0 ≤ clamp01 t := le_min zero_le_one (le_max_left _ _)

/-- The clamp is at most `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem clamp01_le_one (t : ℝ) : clamp01 t ≤ 1 := min_le_left _ _

/-- The clamp is the identity on `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem clamp01_eq_self {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : clamp01 t = t := by
  unfold clamp01
  rw [max_eq_right h0, min_eq_right h1]

end Cleanroom.Deference.DefDoseResponse
