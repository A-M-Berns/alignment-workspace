import Cleanroom.Li.TtLadder.Witnesses

/-!
# `tt-ladder`: witnesses II — the solid-gate witnesses (park, gap, alternating) and Cor 5's limits

Target 5 of [[tt-ladder-mandate]], continued: the sources' constant witnesses shipped exactly
(graded `N−` where constant) beside non-constant perturbations graded `N+`, all under the solid
gate `G ≡ 1` (`a ≡ 3/5` at `t = 1/2, δ = 1/10`; `a ≡ 7/8` at `t = 3/4, δ = 1/8`).

* **park** (W5): `e ≡ t − ε/2 = 2/5` at `ε = 1/5`: `T(t,ε,δ)` with weight `0`, `¬L_prod`,
  `¬GatedMean`, and `¬T(t, ε/4, δ)` — the note's parked-credence example (faithful l.138) is a
  correct witness for `T(t,ε) ⇏ L_prod` (the strictness of Prop A's single instance); the slack
  it illustrates is single-margin, and the FA chat's gloss that it "costs nothing" is false: the
  parked credence is *forbidden* by `T_∀ε`. **park′**: `2/5 ± 1/40` alternating, same
  verdicts, non-constant.
* **gap**: `e ≡ t − ε − δ/2 = 9/16` at `t = 3/4, ε = δ = 1/8`: `Avg` holds (`9/16 ≥ 1/2`),
  `T` fails (weight `1/2`) — the δ gap of root-fa-007.
* **alt** (W6): `e` alternating `1, 0`: the gated mean is `≥ 1/2` at every `N` (so `Avg` and
  `GatedMean` at `t = 1/2` and at root-deference-052's `t = 2/5`), while `T` and `L_prod` fail
  on the odd days, at `t = 1/2` and at `t = 2/5` — no mean inequality encodes `∑ w < ∞`.
* **The averaged lemma's package** under the solid gate: creep has four deep days and a weight
  that is `0` from day `8` (`averaged_package_solid_creep`) — gap and alt are strictness
  witnesses, not package witnesses (their weights are not summable).
* **Cor 5's limits** (root-fa-021): one-sided (`e ≡ 1` passes every rung, `N−`), its mirror the
  silent-quote floor (`a ≡ 0` passes every fixed-`t` rung and the proviso against every `e`,
  `N−`), and rate-free (`N` days of weight `1` under dominance, for every `N`; the quote falls
  silent after day `N`).

Over real sequences; nothing here is a theorem about inductors.
-/

namespace Cleanroom.Li.TtLadder

open LogicalInduction Filter Topology Finset
open Cleanroom.Found.LiAsympCalc

/-! ## The solid gate's mass -/

/-- `prefixSum (fun _ => 1) n = n + 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem prefixSum_one (n : ℕ) : prefixSum (fun _ => (1 : ℝ)) n = (n : ℝ) + 1 := by
  simp [prefixSum]

/-- The mass of the solid gate diverges.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem tendsto_prefixSum_one : Tendsto (prefixSum (fun _ => (1 : ℝ))) atTop atTop := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  exact h.congr (fun n => (prefixSum_one n).symm)

/-- The gate of a constant quote `q` with `t + δ ≤ q` is identically `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem gateSeq_const_eq_one {t δ : ℚ} (hδ : 0 < δ) {q : ℝ} (hq : (t : ℝ) + δ ≤ q) (n : ℕ) :
    gateSeq t δ (fun _ => q) n = 1 :=
  (ctsInd_eq_one_iff hδ _ _).2 (by linarith)

/-- A constant weight `m > 0` is not summable.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem not_summable_const_of_pos {f : ℕ → ℝ} {m : ℝ} (hm : 0 < m) (hf : ∀ n, f n = m) :
    ¬ Summable f := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.1 (summable_eventually_lt h hm)
  have := hN N le_rfl
  rw [hf] at this
  exact lt_irrefl _ this

/-- Under the solid gate the violation weight is the bare ramp `Ind_δ(e_n < t − ε)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem viol_const_quote {t ε δ : ℚ} (hδ : 0 < δ) {q : ℝ} (hq : (t : ℝ) + δ ≤ q) (e : ℕ → ℝ)
    (n : ℕ) : viol e (fun _ => q) t ε δ n = ctsInd δ ((t : ℝ) - ε) (e n) := by
  rw [viol_eq_gateSeq_mul, gateSeq_const_eq_one hδ hq, one_mul]

/-! ## Park (W5) -/

/-- **Park, `T`**: the credence parked at `t − ε/2 = 2/5` (`t = 1/2`, `ε = 1/5`) has weight
identically `0`, so `T(1/2, 1/5, 1/10)` holds.
Source: [[faithful-acceleration]] l.138; lean-deference-2-003 (W5); trust-lab-062 (park); root-deference-2-006 (i)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem tSeq_park : TSeq (fun _ => 3/5) (fun _ => 2/5) (1/2) (1/5) (1/10) := by
  unfold TSeq
  refine summable_zero.congr (fun n => ?_)
  rw [viol_const_quote (by norm_num) (by norm_num), (ctsInd_eq_zero_iff (by norm_num) _ _).2
    (by norm_num)]

/-- **Park, `¬L_prod`**: `G (e − t) ≡ −1/10`.
Source: [[faithful-acceleration]] l.138 ("but the limit fails"); trust-lab-062
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem not_lProdSeq_park : ¬ LProdSeq (fun _ => 3/5) (fun _ => 2/5) (1/2) (1/10) := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h (1/20) (by norm_num))
  have h1 : (0 : ℝ) ≤ gateSeq (1/2) (1/10) (fun _ => 3/5) N * ((2/5 : ℝ) - ((1/2 : ℚ) : ℝ))
      + 1/20 := hN N le_rfl
  rw [gateSeq_const_eq_one (by norm_num) (by norm_num)] at h1
  norm_num at h1

/-- **Park, `¬GatedMean`**: the gate mass diverges and the gated mean of `2/5` is `2/5 < 1/2`
("mean < t while `∑ w < ∞`", trust-lab-062).
Source: trust-lab-062 (park: "also mean < t while Σw < ∞"); [[faithful-acceleration]] l.140
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem not_gatedMeanSeq_park : ¬ GatedMeanSeq (fun _ => 3/5) (fun _ => 2/5) (1/2) (1/10) := by
  intro h
  have hdiv : Tendsto (prefixSum (gateSeq (1/2) (1/10) (fun _ => 3/5))) atTop atTop :=
    tendsto_prefixSum_one.congr (fun n => by
      unfold prefixSum
      exact Finset.sum_congr rfl (fun i _ => (gateSeq_const_eq_one (by norm_num) (by norm_num) i).symm))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h hdiv (1/20) (by norm_num))
  have h1 := hN N le_rfl
  have hden : prefixSum (gateSeq (1/2) (1/10) (fun _ => 3/5)) N ≠ 0 := by
    have : prefixSum (gateSeq (1/2) (1/10) (fun _ => 3/5)) N = (N : ℝ) + 1 := by
      rw [← prefixSum_one]
      unfold prefixSum
      exact Finset.sum_congr rfl (fun i _ => gateSeq_const_eq_one (by norm_num) (by norm_num) i)
    rw [this]; positivity
  rw [weightedAverage_const _ _ hden] at h1
  norm_num at h1

/-- **Park, `¬T` at the quarter margin**: at `ε' = ε/4 = 1/20` the weight is identically `1/2`
(`ctsInd (1/10) (9/20) (2/5) = 1/2`), so the parked credence is forbidden by `T_∀ε`. The slack
that [[faithful-acceleration]] l.138 illustrates with this credence is a *single-margin* slack:
the note's sentence is a correct strictness witness for `T(t,ε) ⇏ L_prod` (`tSeq_not_lProdSeq`),
and it is the FA chat's / lean-deference-046's gloss "costs nothing" (D11) — not the note — that
this theorem refutes: the theorem family, at every rational margin, grants no parked shortfall.
Source: lean-deference-2-003 (W5, "the instance at `ε' = ε/4` fails", D11); lean-deference-046 (the "costs nothing" gloss on faithful l.138)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem not_tSeq_park_quarter : ¬ TSeq (fun _ => 3/5) (fun _ => 2/5) (1/2) (1/20) (1/10) := by
  unfold TSeq
  refine not_summable_const_of_pos (m := 1/2) (by norm_num) (fun n => ?_)
  rw [viol_const_quote (by norm_num) (by norm_num), ctsInd_of_le (by norm_num) (by norm_num)]
  norm_num

/-- **Park** (W5, `N−`: the source's constant witness, shipped exactly): `a ≡ 3/5`, `e ≡ 2/5`
at `t = 1/2, ε = 1/5, δ = 1/10`: `T` holds with weight `0`, `L_prod` fails, the gated mean
fails, and `T` at `ε/4` fails.
Source: [[faithful-acceleration]] l.138; lean-deference-2-003 (W5); trust-lab-062 (park)
Kind: N−
Fidelity: exact
Hyps: n/a -/
theorem park_witness :
    (∀ n, (fun _ : ℕ => (3/5 : ℝ)) n ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ n, (fun _ : ℕ => (2/5 : ℝ)) n ∈ Set.Icc (0 : ℝ) 1) ∧
    TSeq (fun _ => 3/5) (fun _ => 2/5) (1/2) (1/5) (1/10) ∧
    ¬ LProdSeq (fun _ => 3/5) (fun _ => 2/5) (1/2) (1/10) ∧
    ¬ GatedMeanSeq (fun _ => 3/5) (fun _ => 2/5) (1/2) (1/10) ∧
    ¬ TSeq (fun _ => 3/5) (fun _ => 2/5) (1/2) (1/20) (1/10) :=
  ⟨fun _ => ⟨by norm_num, by norm_num⟩, fun _ => ⟨by norm_num, by norm_num⟩, tSeq_park,
    not_lProdSeq_park, not_gatedMeanSeq_park, not_tSeq_park_quarter⟩

/-- The perturbed parked credence `2/5 ± 1/40`, alternating with the parity of `n`.
Source: [[tt-ladder-mandate]] target 5 (park′)
Kind: D
Fidelity: variant: non-constant perturbation of W5
Hyps: n/a -/
noncomputable def parkE' (n : ℕ) : ℝ := if Even n then 2/5 + 1/40 else 2/5 - 1/40

/-- `parkE' n ∈ [3/8, 17/40]`.
Source: [[tt-ladder-mandate]] target 5
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem parkE'_bounds (n : ℕ) : 3/8 ≤ parkE' n ∧ parkE' n ≤ 17/40 := by
  unfold parkE'
  split_ifs <;> norm_num

/-- **Park′** (`N+`, non-constant credence): `a ≡ 3/5`, `e n = 2/5 ± 1/40`: `T(1/2, 1/5, 1/10)`
holds with weight `0` (`e ≥ 3/8 ≥ t − ε`), `L_prod` fails (`G (e − t) ≤ −3/40`).
Source: [[tt-ladder-mandate]] target 5 (park′); [[faithful-acceleration]] l.138
Kind: N+
Fidelity: variant: non-constant perturbation of W5
Hyps: n/a -/
theorem park'_witness :
    (∀ n, (fun _ : ℕ => (3/5 : ℝ)) n ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ n, parkE' n ∈ Set.Icc (0 : ℝ) 1) ∧
    TSeq (fun _ => 3/5) parkE' (1/2) (1/5) (1/10) ∧
    ¬ LProdSeq (fun _ => 3/5) parkE' (1/2) (1/10) := by
  refine ⟨fun _ => ⟨by norm_num, by norm_num⟩,
    fun n => ⟨by linarith [(parkE'_bounds n).1], by linarith [(parkE'_bounds n).2]⟩, ?_, ?_⟩
  · unfold TSeq
    refine summable_zero.congr (fun n => ?_)
    rw [viol_const_quote (by norm_num) (by norm_num),
      (ctsInd_eq_zero_iff (by norm_num) _ _).2 (by push_cast; linarith [(parkE'_bounds n).1])]
  · intro h
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h (1/40) (by norm_num))
    have h1 : (0 : ℝ) ≤ gateSeq (1/2) (1/10) (fun _ => 3/5) N * (parkE' N - ((1/2 : ℚ) : ℝ))
        + 1/40 := hN N le_rfl
    rw [gateSeq_const_eq_one (by norm_num) (by norm_num), one_mul] at h1
    push_cast at h1
    linarith [(parkE'_bounds N).2]

/-- **Non-arrow `T(t,ε,δ) ⇏ L_prod`** at `t = 1/2, ε = 1/5, δ = 1/10` (park′, non-constant):
with `lProdSeq_not_tSeq`, `L_prod` and single-instance `T` are incomparable; with
`not_tSeq_park_quarter`, the parked credence is excluded by `T_∀ε`. The note's l.138 example
(park) is a correct witness for exactly this direction — the strictness of the single instance
`T(t,ε)` against `L_prod`, hence of (ii) `T_∀ε ⇒ T(t,ε)` — and the slack it illustrates is
single-margin (F3).
Source: lean-deference-2-002 ("`T(t,ε) ⇏ L_prod` (W5)"); [[faithful-acceleration]] l.138
Kind: N+
Fidelity: variant: sequence-level
Hyps: n/a -/
theorem tSeq_not_lProdSeq :
    ∃ a e : ℕ → ℝ, (∀ n, a n ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ n, e n ∈ Set.Icc (0 : ℝ) 1) ∧
      TSeq a e (1/2) (1/5) (1/10) ∧ ¬ LProdSeq a e (1/2) (1/10) :=
  ⟨_, _, park'_witness.1, park'_witness.2.1, park'_witness.2.2.1, park'_witness.2.2.2⟩

/-- **Non-arrow `T(t,ε,δ) ⇏ GatedMean`** (park): the bare gated mean is not implied by summable
violation weight (root-fa-007's last sentence, first half).
Source: root-fa-007; [[faithful-acceleration]] l.140; trust-lab-062
Kind: N−
Fidelity: variant: sequence-level
Hyps: n/a -/
theorem tSeq_not_gatedMeanSeq :
    ∃ a e : ℕ → ℝ, (∀ n, a n ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ n, e n ∈ Set.Icc (0 : ℝ) 1) ∧
      TSeq a e (1/2) (1/5) (1/10) ∧ ¬ GatedMeanSeq a e (1/2) (1/10) :=
  ⟨_, _, park_witness.1, park_witness.2.1, park_witness.2.2.1, park_witness.2.2.2.2.1⟩

/-! ## Gap -/

/-- **Gap, `Avg`**: `e ≡ t − ε − δ/2 = 9/16` under the solid gate `a ≡ 7/8` at `t = 3/4`,
`ε = δ = 1/8`: the gated mean is `9/16 ≥ 1/2 = t − ε − δ`, so `Avg` holds.
Source: trust-lab-062 (gap); root-fa-007 ("the δ gap"); [[faithful-acceleration]] l.168–169
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem avgSeq_gap : AvgSeq (fun _ => 7/8) (fun _ => 9/16) (3/4) (1/8) (1/8) := by
  intro hdiv η hη
  filter_upwards [eventually_prefixSum_pos hdiv] with N hpos
  show ((3/4 : ℚ) : ℝ) - ((1/8 : ℚ) : ℝ) - ((1/8 : ℚ) : ℝ) ≤
    weightedAverage (gateSeq (3/4) (1/8) (fun _ => 7/8)) (fun _ => 9/16) N + η
  rw [weightedAverage_const _ _ hpos.ne']
  push_cast
  linarith

/-- **Gap, `¬T`**: the weight is identically `1/2` (`ctsInd (1/8) (5/8) (9/16) = 1/2`).
Source: trust-lab-062 (gap: "`w_n = ½`, `Σ w = ∞`")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem not_tSeq_gap : ¬ TSeq (fun _ => 7/8) (fun _ => 9/16) (3/4) (1/8) (1/8) := by
  unfold TSeq
  refine not_summable_const_of_pos (m := 1/2) (by norm_num) (fun n => ?_)
  rw [viol_const_quote (by norm_num) (by norm_num), ctsInd_of_le (by norm_num) (by norm_num)]
  norm_num

/-- **Non-arrow `Avg ⇏ T`** (gap, `N−`: constant): the Corollary is strictly weaker than the
Theorem by the `δ` gap. The non-constant witness is `avgSeq_not_tSeq_alt` below.
Source: trust-lab-062 (gap); root-fa-007; [[faithful-acceleration]] l.168–169
Kind: N−
Fidelity: variant: sequence-level
Hyps: n/a -/
theorem avgSeq_not_tSeq_gap :
    ∃ a e : ℕ → ℝ, (∀ n, a n ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ n, e n ∈ Set.Icc (0 : ℝ) 1) ∧
      AvgSeq a e (3/4) (1/8) (1/8) ∧ ¬ TSeq a e (3/4) (1/8) (1/8) :=
  ⟨_, _, fun _ => ⟨by norm_num, by norm_num⟩, fun _ => ⟨by norm_num, by norm_num⟩, avgSeq_gap,
    not_tSeq_gap⟩

/-! ## Alternating (W6) -/

/-- The alternating credence `1, 0, 1, 0, …`.
Source: [[li-deference]] l.220–224 (root-deference-052); lean-deference-2-003 (W6); trust-lab-062 (alt)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def altE (n : ℕ) : ℝ := if Even n then 1 else 0

/-- `altE n ∈ [0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem altE_mem_Icc (n : ℕ) : altE n ∈ Set.Icc (0 : ℝ) 1 := by
  unfold altE; split_ifs <;> norm_num

/-- `∑_{i < N} altE i = ⌈N/2⌉ = (N + 1) / 2` (natural division).
Source: trust-lab-062 (`ladder_check.py` [E4])
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem sum_altE (N : ℕ) : ∑ i ∈ range N, altE i = (((N + 1) / 2 : ℕ) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    unfold altE
    by_cases h : Even N
    · rw [if_pos h]
      rw [Nat.even_iff] at h
      norm_cast
      omega
    · rw [if_neg h]
      rw [Nat.even_iff] at h
      norm_cast
      omega

/-- **The finite-`N` mean inequality** (`ladder_check.py` [E4]): under the solid gate the gated
mean of `altE` is at least `1/2` on every day `N`.
Source: root-deference-052; trust-lab-062 (alt: "bare gated mean ≥ t for every N ≥ 1")
Kind: P
Fidelity: stronger: `≥ 1/2` at every `N` (the sources need `≥ 2/5`)
Hyps: (a) none -/
theorem weightedAverage_one_altE_ge (N : ℕ) :
    1/2 ≤ weightedAverage (fun _ => (1 : ℝ)) altE N := by
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hden : prefixSum (fun _ => (1 : ℝ)) N ≠ 0 := by rw [prefixSum_one]; exact hpos.ne'
  rw [weightedAverage_eq_div hden, prefixSum_one, le_div_iff₀ hpos]
  unfold prefixSum
  simp only [one_mul]
  rw [sum_altE]
  have : (N : ℝ) + 1 ≤ 2 * (((N + 1 + 1) / 2 : ℕ) : ℝ) := by
    have h : N + 1 ≤ 2 * ((N + 1 + 1) / 2) := by omega
    exact_mod_cast h
  linarith

/-- The solid gate at `(t, δ)` with `t + δ ≤ 3/5` equals `1`, so its weighted average of `altE`
is the uniform one.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem weightedAverage_gateSeq_altE {t δ : ℚ} (hδ : 0 < δ) (h : (t : ℝ) + δ ≤ 3/5) (N : ℕ) :
    weightedAverage (gateSeq t δ (fun _ => 3/5)) altE N = weightedAverage (fun _ => 1) altE N := by
  have : gateSeq t δ (fun _ => (3/5 : ℝ)) = fun _ => 1 := funext (gateSeq_const_eq_one hδ h)
  rw [this]

/-- **Alt, `Avg` and `GatedMean`**: at `t = 1/2, ε = δ = 1/10` and at `t = 2/5`, the alternating
credence under the solid gate satisfies the averaged rung and the bare gated mean (its mean
is `≥ 1/2` on every day).
Source: [[li-deference]] l.220–224 (root-deference-052, `t = 2/5`); lean-deference-2-003 (W6); trust-lab-062 (alt)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem avgSeq_gatedMeanSeq_alt :
    AvgSeq (fun _ => 3/5) altE (1/2) (1/10) (1/10) ∧
    GatedMeanSeq (fun _ => 3/5) altE (1/2) (1/10) ∧
    GatedMeanSeq (fun _ => 3/5) altE (2/5) (1/10) := by
  refine ⟨fun _ η hη => ?_, fun _ η hη => ?_, fun _ η hη => ?_⟩ <;>
  · refine Eventually.of_forall (fun N => ?_)
    have := weightedAverage_one_altE_ge N
    show _ ≤ weightedAverage (gateSeq _ _ (fun _ => 3/5)) altE N + η
    rw [weightedAverage_gateSeq_altE (by norm_num) (by norm_num)]
    push_cast
    linarith

/-- **Alt, `¬T` and `¬L_prod`** at `t = 1/2, ε = δ = 1/10`: on odd days the weight is `1` and
`G (e − t) = −1/2`.
Source: [[li-deference]] l.220–224; lean-deference-2-003 (W6); trust-lab-062 (alt)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem not_tSeq_not_lProdSeq_alt :
    ¬ TSeq (fun _ => 3/5) altE (1/2) (1/10) (1/10) ∧
    ¬ LProdSeq (fun _ => 3/5) altE (1/2) (1/10) := by
  have hodd : ∀ N : ℕ, altE (2 * N + 1) = 0 := fun N => by
    unfold altE
    rw [if_neg (Nat.not_even_iff_odd.2 (odd_two_mul_add_one N))]
  constructor
  · intro h
    obtain ⟨N, hN⟩ := eventually_atTop.1 (summable_eventually_lt h one_pos)
    have h1 := hN (2 * N + 1) (by omega)
    rw [viol_const_quote (by norm_num) (by norm_num), hodd,
      (ctsInd_eq_one_iff (by norm_num) _ _).2 (by norm_num)] at h1
    exact lt_irrefl _ h1
  · intro h
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h (1/4) (by norm_num))
    have h1 : (0 : ℝ) ≤ gateSeq (1/2) (1/10) (fun _ => 3/5) (2 * N + 1) *
        (altE (2 * N + 1) - ((1/2 : ℚ) : ℝ)) + 1/4 := hN (2 * N + 1) (by omega)
    rw [gateSeq_const_eq_one (by norm_num) (by norm_num), hodd] at h1
    norm_num at h1

/-- **Non-arrow `Avg ⇏ T`** (alt, `N+`: non-constant credence): the average tolerates a
constant fraction of deep violations; "no cancellation" (`faithful-acceleration` l.140).
Source: lean-deference-2-002 ("`Avg ⇏ T(t,ε)` (W6)"); root-deference-052; [[faithful-acceleration]] l.140
Kind: N+
Fidelity: variant: sequence-level
Hyps: n/a -/
theorem avgSeq_not_tSeq_alt :
    ∃ a e : ℕ → ℝ, (∀ n, a n ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ n, e n ∈ Set.Icc (0 : ℝ) 1) ∧
      AvgSeq a e (1/2) (1/10) (1/10) ∧ ¬ TSeq a e (1/2) (1/10) (1/10) :=
  ⟨_, _, fun _ => ⟨by norm_num, by norm_num⟩, altE_mem_Icc, avgSeq_gatedMeanSeq_alt.1,
    not_tSeq_not_lProdSeq_alt.1⟩

/-- **Alt, `¬T` at root-deference-052's threshold**: at `t = 2/5`, `ε = δ = 1/10` the weight is
`1` on every odd day (ramp `ctsInd (1/10) (3/10) 0 = 1`), so `T(2/5, 1/10, 1/10)` fails.
Source: [[li-deference]] l.220–224 (root-deference-052: "take `t = 0.4` … `Σ w_n = #{days at 0} = ∞`")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem not_tSeq_alt_two_fifths : ¬ TSeq (fun _ => 3/5) altE (2/5) (1/10) (1/10) := by
  have hodd : ∀ N : ℕ, altE (2 * N + 1) = 0 := fun N => by
    unfold altE
    rw [if_neg (Nat.not_even_iff_odd.2 (odd_two_mul_add_one N))]
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.1 (summable_eventually_lt h one_pos)
  have h1 := hN (2 * N + 1) (by omega)
  rw [viol_const_quote (by norm_num) (by norm_num), hodd,
    (ctsInd_eq_one_iff (by norm_num) _ _).2 (by norm_num)] at h1
  exact lt_irrefl _ h1

/-- **Non-arrow `GatedMean ⇏ T`** at root-deference-052's threshold `t = 2/5` on *both* sides
(alt, `N+`): `GatedMean(2/5) ∧ ¬T(2/5, 1/10, 1/10)` — gated-average Total Trust does not imply
finite violations at the threshold it is stated for; `∑ w < ∞` is a strengthening of the gated
mean, not its translation. The gate mass is divergent (the solid gate), as `¬T` forces. With
`tSeq_not_gatedMeanSeq`: the bare mean and `∑ w < ∞` are incomparable. The same non-arrow at
`t = 1/2` is `gatedMeanSeq_not_tSeq_half`.
Source: [[li-deference]] l.216–226 (root-deference-052, `t = 0.4` for the mean and the violation sum); root-fa-007 (last sentence)
Kind: N+
Fidelity: variant: sequence-level
Hyps: n/a -/
theorem gatedMeanSeq_not_tSeq :
    ∃ a e : ℕ → ℝ, (∀ n, a n ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ n, e n ∈ Set.Icc (0 : ℝ) 1) ∧
      GatedMeanSeq a e (2/5) (1/10) ∧ ¬ TSeq a e (2/5) (1/10) (1/10) :=
  ⟨_, _, fun _ => ⟨by norm_num, by norm_num⟩, altE_mem_Icc, avgSeq_gatedMeanSeq_alt.2.2,
    not_tSeq_alt_two_fifths⟩

/-- **Non-arrow `GatedMean ⇏ T`** at the package's default threshold `t = 1/2`, one threshold on
both sides (alt, `N+`): `GatedMean(1/2) ∧ ¬T(1/2, 1/10, 1/10)`.
Source: [[li-deference]] l.216–226 (root-deference-052); lean-deference-2-003 (W6)
Kind: N+
Fidelity: variant: sequence-level
Hyps: n/a -/
theorem gatedMeanSeq_not_tSeq_half :
    ∃ a e : ℕ → ℝ, (∀ n, a n ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ n, e n ∈ Set.Icc (0 : ℝ) 1) ∧
      GatedMeanSeq a e (1/2) (1/10) ∧ ¬ TSeq a e (1/2) (1/10) (1/10) :=
  ⟨_, _, fun _ => ⟨by norm_num, by norm_num⟩, altE_mem_Icc, avgSeq_gatedMeanSeq_alt.2.1,
    not_tSeq_not_lProdSeq_alt.1⟩

/-! ## The averaged lemma's full package under the solid gate -/

/-- **Witness of the averaged lemma's full package under the solid gate** (`N+`, non-constant
credence with finitely many deep days): `G ≡ 1` (from `a ≡ 3/5`) against the creeping credence
`creepE n = 1/2 − 1/(n+2)` at `t = 1/2`, `ε = δ = 1/10`. The deep days (`e_n ≤ t − ε − δ = 3/10`)
are exactly days `0..3`, where the weight is `1`; from day `8` the weight is `0`; so the margin
weight is summable, the gate mass diverges, and `averaged_of_summable` gives the gated average
`≳ₙ 3/10`. This is root-fa-006's own suggestion for a package witness ("`g ≡ 1`, `e` above
`t − ε − δ` with finitely many deep days"); the non-constant-gate companion is
`averaged_package_harmonic_creep` (`Witnesses.lean`). Gap and alt are *not* package witnesses:
they fail the summability hypothesis (their weights are `≡ 1/2` and `1` on odd days), which is
why they witness the strictness `Avg ∧ ¬T` instead.
Source: [[tt-ladder-mandate]] target 4 ("Witness for the lemma's full package (`N+`): `g ≡ 1`, `e` … with finitely many deep days"); root-fa-006
Kind: N+
Fidelity: variant: sequence-level (creeping rather than oscillating `e`; four deep days)
Hyps: n/a -/
theorem averaged_package_solid_creep :
    (∀ n, gateSeq (1/2) (1/10) (fun _ => 3/5) n = 1) ∧
    (∀ n, 0 ≤ creepE n) ∧
    Tendsto (prefixSum (gateSeq (1/2) (1/10) (fun _ => 3/5))) atTop atTop ∧
    (∀ n, n < 4 → gateSeq (1/2) (1/10) (fun _ => 3/5) n *
      ctsInd (1/10) (((1/2 : ℚ) : ℝ) - ((1/10 : ℚ) : ℝ)) (creepE n) = 1) ∧
    Summable (fun n => gateSeq (1/2) (1/10) (fun _ => 3/5) n *
      ctsInd (1/10) (((1/2 : ℚ) : ℝ) - ((1/10 : ℚ) : ℝ)) (creepE n)) ∧
    AsympGE (weightedAverage (gateSeq (1/2) (1/10) (fun _ => 3/5)) creepE)
      (fun _ => ((1/2 : ℚ) : ℝ) - ((1/10 : ℚ) : ℝ) - ((1/10 : ℚ) : ℝ)) := by
  have hg1 : ∀ n, gateSeq (1/2) (1/10) (fun _ => (3/5 : ℝ)) n = 1 := gateSeq_const_three_fifths
  have hg : ∀ n, gateSeq (1/2) (1/10) (fun _ => (3/5 : ℝ)) n ∈ Set.Icc (0 : ℝ) 1 :=
    gateSeq_mem_Icc _ _ _
  have he : ∀ n, 0 ≤ creepE n := fun n => (creepE_bounds n).1
  have hdiv : Tendsto (prefixSum (gateSeq (1/2) (1/10) (fun _ => (3/5 : ℝ)))) atTop atTop := by
    have : gateSeq (1/2) (1/10) (fun _ => (3/5 : ℝ)) = fun _ => 1 := funext hg1
    rw [this]
    exact tendsto_prefixSum_one
  have hs := summable_mul_ramp_creepE (gateSeq (1/2) (1/10) (fun _ => 3/5))
  refine ⟨hg1, he, hdiv, fun n hn => ?_, hs, averaged_of_summable (by norm_num) hg he hdiv hs⟩
  rw [hg1, one_mul, (ctsInd_eq_one_iff (by norm_num) _ _).2 ?_]
  unfold creepE
  push_cast
  interval_cases n <;> norm_num

/-! ## Cor 5's built-in limits -/

/-- **One-sided** (`N−`, the point of the row): the constant credence `e ≡ 1` satisfies `T_full`
at every width, `BV` at every threshold and `L_cond` at every threshold, for *every*
`[0,1]`-valued quote `a` — nothing in the family constrains days on which the credence exceeds
the quote.
Source: root-fa-021 (Cor 5, "one-sided")
Kind: N−
Fidelity: variant: sequence-level
Hyps: n/a -/
theorem one_sided_ceiling (a : ℕ → ℝ) (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1) {δ : ℚ} (hδ : 0 < δ) :
    TFullSeq a (fun _ => 1) δ ∧ (∀ t : ℚ, BVSeq a (fun _ => 1) t δ) ∧
      ∀ t : ℚ, LCondSeq a (fun _ => 1) t := by
  have hdom : Dominates (fun _ => 1) a := fun c hc =>
    Eventually.of_forall (fun n => by linarith [(ha n).2])
  refine ⟨tFullSeq_of_dominates hδ hdom, fun t => ?_, lCondSeq_of_dominates hdom⟩
  unfold BVSeq
  refine summable_zero.congr (fun n => ?_)
  rcases le_or_gt (t : ℝ) 1 with ht | ht
  · rw [(ctsInd_eq_zero_iff hδ _ _).2 ht, mul_zero]
  · rw [(gateSeq_eq_zero_iff hδ a n).2 (by linarith [(ha n).2]), zero_mul]

/-- **The silent-quote floor** (`N−`, the mirror of `one_sided_ceiling`): on a quote that never
exceeds the threshold (`a ≡ 0` at `t = 1/2`, `δ = 1/10`) every fixed-`t` predicate of
`Defs.lean` — `T`, `T_∀ε`, `BV`, `L_prod`, `L_cond`, `Avg`, `GatedMean` — *and* the proviso
`SupportNondegenerate` hold for every credence `e` and every margin `ε`: a gate that never opens
constrains nothing, so the whole fixed-`t` diagram, `middle_rung_repaired_iff` included, says
nothing there. Inherent to the sources' semantics; recorded so both trivial ends of "one-sided"
are kernel-visible.
Source: [[tt-ladder-audit-r1-adversarial]] N-a (probe A1); root-fa-021 (Cor 5, "one-sided")
Kind: N−
Fidelity: variant: sequence-level
Hyps: n/a -/
theorem silent_quote_floor (e : ℕ → ℝ) (ε : ℚ) :
    TSeq (fun _ => 0) e (1/2) ε (1/10) ∧ TAllEpsSeq (fun _ => 0) e (1/2) (1/10) ∧
    BVSeq (fun _ => 0) e (1/2) (1/10) ∧ LProdSeq (fun _ => 0) e (1/2) (1/10) ∧
    LCondSeq (fun _ => 0) e (1/2) ∧ AvgSeq (fun _ => 0) e (1/2) ε (1/10) ∧
    GatedMeanSeq (fun _ => 0) e (1/2) (1/10) ∧
    SupportNondegenerate (1/2) (1/10) (fun _ => 0) := by
  have hg : ∀ n, gateSeq (1/2) (1/10) (fun _ => (0 : ℝ)) n = 0 := fun n =>
    (gateSeq_eq_zero_iff (by norm_num) _ n).2 (by show (0 : ℝ) ≤ ((1/2 : ℚ) : ℝ); norm_num)
  have hv : ∀ ε' : ℚ, ∀ n, viol e (fun _ => 0) (1/2) ε' (1/10) n = 0 := fun ε' n => by
    rw [viol_eq_gateSeq_mul, hg, zero_mul]
  have hps : ∀ N, prefixSum (gateSeq (1/2) (1/10) (fun _ => (0 : ℝ))) N = 0 := fun N => by
    unfold prefixSum
    exact Finset.sum_eq_zero (fun i _ => hg i)
  have hndiv : ¬ Tendsto (prefixSum (gateSeq (1/2) (1/10) (fun _ => (0 : ℝ)))) atTop atTop := by
    intro h
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h.eventually (eventually_gt_atTop 0))
    have := hN N le_rfl
    rw [hps] at this
    exact lt_irrefl _ this
  refine ⟨?_, ?_, ?_, ?_, ?_, fun h => absurd h hndiv, fun h => absurd h hndiv,
    ⟨1, one_pos, fun n hn => by rw [hg] at hn; exact absurd hn (lt_irrefl _)⟩⟩
  · unfold TSeq
    exact summable_zero.congr (fun n => (hv ε n).symm)
  · intro ε' _
    unfold TSeq
    exact summable_zero.congr (fun n => (hv ε' n).symm)
  · unfold BVSeq
    exact summable_zero.congr (fun n => by rw [hg, zero_mul])
  · intro η hη
    refine Eventually.of_forall (fun n => ?_)
    show (0 : ℝ) ≤ gateSeq (1/2) (1/10) (fun _ => 0) n * (e n - ((1/2 : ℚ) : ℝ)) + η
    rw [hg, zero_mul, zero_add]
    exact hη.le
  · intro c _
    refine Eventually.of_forall (fun n hn => ?_)
    exfalso
    have : ((1/2 : ℚ) : ℝ) < 0 := hn
    push_cast at this
    linarith

/-- **Rate-free** (`N+`): for every `N` there are `[0,1]`-valued `a, e` with `Dominates e a`
(hence `T_full` at every width) and weight exactly `1` on each of the first `N` days — nothing
in the family bounds how long "finitely many" lasts. The witness is a block: `a = 1` on days
`n < N` and `0` after, against `e ≡ 0`; `Dominates` holds because the quote falls *silent* after
day `N`, so this is not a persistently flagging quote (for one, use `rate_free`'s block followed
by any dominated tail).
Source: root-fa-021 (Cor 5, "rate-free")
Kind: N+
Fidelity: variant: sequence-level
Hyps: n/a -/
theorem rate_free (N : ℕ) :
    ∃ a e : ℕ → ℝ, (∀ n, a n ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ n, e n ∈ Set.Icc (0 : ℝ) 1) ∧
      Dominates e a ∧ ∀ n, n < N → viol e a (1/2) (1/4) (1/10) n = 1 := by
  refine ⟨fun n => if n < N then 1 else 0, fun _ => 0, fun n => ?_, fun _ => ⟨le_rfl, zero_le_one⟩,
    fun c hc => ?_, fun n hn => ?_⟩
  · show (if n < N then (1 : ℝ) else 0) ∈ Set.Icc (0 : ℝ) 1
    split_ifs <;> norm_num
  · filter_upwards [eventually_ge_atTop N] with n hn
    rw [if_neg (not_lt.2 hn)]
    linarith
  · rw [viol_eq_gateSeq_mul]
    unfold gateSeq
    show ctsInd (1/10) (if n < N then (1 : ℝ) else 0) ((1/2 : ℚ) : ℝ) *
      ctsInd (1/10) (((1/2 : ℚ) : ℝ) - ((1/4 : ℚ) : ℝ)) 0 = 1
    rw [if_pos hn, (ctsInd_eq_one_iff (by norm_num) _ _).2 (by norm_num),
      (ctsInd_eq_one_iff (by norm_num) _ _).2 (by norm_num), one_mul]

end Cleanroom.Li.TtLadder
