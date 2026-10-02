import Cleanroom.Li.LiPseudorandom.Family
import Cleanroom.Li.LiPseudorandom.Deferral
import Cleanroom.Li.LiPseudorandom.Joint
import Cleanroom.Li.LiPseudorandom.Union
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# `li-pseudorandom` — the N+ witnesses

Every headline's hypothesis package is inhabited, and the objects are non-degenerate:

* **T1.** `constRule` (weight `1` every day) and `evenRule` (weight `1` on even days) are
  `CausalRule`s with divergent realized sums on every stream; for any rule family with
  `R 0 = constRule` and `p ∈ (0,1)`, `diag R p` is **not eventually constant**
  (`diag_not_eventuallyConst`: its density is `p`), and with `R 1 = evenRule` its density on even
  days is also `p` (`diag_even_density`). At `p = 1/2` and the constant rules, the first two values
  are `false, true` (`diag_const_half_zero`, `diag_const_half_one`): the second day compensates the
  first, computed by hand from the finite potential (no `native_decide`).
* **T1, adaptive clause.** `prevRule` (weight `1` after a `true` day) reads the stream; with
  `R 0 = constRule`, `R 1 = prevRule`, its realized sum on the diagonal diverges and the truth
  frequency after `true` days is `p` (`diag_prev_density`; repair round 1).
* **T4.** Over **any** history `P`, with the constant P-generable weighting `EF.const 1` (FAF's
  `constantRatFeature_generated`), the fixed-history family has density `p` and is not eventually
  constant (`diagBuilder_history_not_eventuallyConst`); the real-market instance is over the LIA
  of a fixed decided family (`diagBuilder_liaHistory_not_eventuallyConst`; repair round 1, replacing
  the mandate's constant market `P ≡ 1/2`, which [[STANDARDS]] §3 calls trivial).
* **T9 and the union shape.** The two-family stream (`truthStar₂_not_eventuallyConst`, via
  `not_eventuallyConst_of_varied_average`), each of its subfamilies
  (`truthStar₂_even_not_eventuallyConst`, `truthStar₂_odd_not_eventuallyConst`; repair round 2),
  every family of the countable-family stream (`truthStarω_family_not_eventuallyConst`; repair
  round 2) and the family inside a union process (`unionStar_not_eventuallyConst`) are not
  eventually constant.
* **The hypotheses do work** (repair round 2, adopting the round-2 adversarial probe
  `Vacuity.lean`). The omniscient builder `omniscient x m _ := truthR x m` is a `CausalBuilder`
  for the non-strict profile `g = id` and is *not* one for delay one
  (`omniscient_causalBuilder_id`, `omniscient_not_causalBuilder_succ`): the strictness
  `∀ j, j < g j` in T5/T6 excludes exactly the market the mandate's § Context 1 says defeats
  every fixed family. The trivial enumeration `fun _ _ => EF.const 0` does not cover the
  P-generable weightings (`trivial_enumeration_does_not_cover`): T5's `hcov` is not free.
* **The market of record varies with the stream**: `Market.lean` (`builder_not_const`), by
  FAF's criterion on certified inductors over constant streams.
* **T5.** The toy builder `toyBuilder x m φ := truthR x (m − 1)` (`1/2` on day `0`) is causal
  for delay `n + 1` and not constant (`toyBuilder_causal`, `toyBuilder_nonconst`); the real
  instance is T6's `liaHistory (atomDP a x g)` (`liaHistory_atomDP_causal`).
* **T6.** The family of record `truthStar a g p` at `p ∈ (0,1)` is not eventually constant
  (`truthStar_not_eventuallyConst`, through the const-`1` P-generable weighting on the LIA), and
  its process is not trivial: every stage is strictly contained in a later one
  (`atomDP_stage_ssubset`), so its stages grow without bound.

Grade **N+** throughout: a real inductor construction (`liaHistory`), non-constant streams, a
process with growing stages; no empty types, no constant sequences, no trivial market.
-/

namespace Cleanroom.Li.LiPseudorandom

open LogicalInduction Filter Topology
open scoped BigOperators

/-! ## Rules -/

/-- The constant rule: weight `1` on every day, every stream.
Source: mandate T1 (witness)
Kind: D
Fidelity: n/a -/
def constRule : CausalRule where
  w _ _ := 1
  nonneg _ _ := zero_le_one
  le_one _ _ := le_rfl
  causal _ _ _ _ := rfl

/-- The even-day rule: weight `1` on even days, `0` on odd days.
Source: mandate T1 (witness)
Kind: D
Fidelity: n/a -/
noncomputable def evenRule : CausalRule where
  w _ n := if Even n then 1 else 0
  nonneg _ n := by split_ifs <;> norm_num
  le_one _ n := by split_ifs <;> norm_num
  causal _ _ _ _ := rfl

/-- The prefix sum of the constant `1` is `n + 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prefixSum_const_one (n : ℕ) : prefixSum (fun _ => (1 : ℝ)) n = (n : ℝ) + 1 := by
  simp [prefixSum]

/-- The constant-`1` weighting diverges.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tendsto_prefixSum_const_one : Tendsto (prefixSum (fun _ => (1 : ℝ))) atTop atTop := by
  have h : prefixSum (fun _ => (1 : ℝ)) = fun n : ℕ => (n : ℝ) + 1 := funext prefixSum_const_one
  rw [h]
  exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

/-- Even-day indicator sums: `∑_{j < 2m} [Even j] = m`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_evenInd_range_two_mul (m : ℕ) :
    ∑ j ∈ Finset.range (2 * m), (if Even j then (1 : ℝ) else 0) = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h1 : Even (2 * m) := even_two_mul m
    have h2 : ¬ Even (2 * m + 1) := Nat.not_even_iff_odd.2 (odd_two_mul_add_one m)
    simp [h1, h2]

/-- The even-day weighting diverges.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tendsto_prefixSum_evenInd :
    Tendsto (prefixSum (fun n => if Even n then (1 : ℝ) else 0)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨2 * ⌈b⌉₊, fun n hn => ?_⟩
  have hnonneg : ∀ j : ℕ, 0 ≤ (if Even j then (1 : ℝ) else 0) := fun j => by split_ifs <;> norm_num
  calc b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
    _ = ∑ j ∈ Finset.range (2 * ⌈b⌉₊), (if Even j then (1 : ℝ) else 0) :=
        (sum_evenInd_range_two_mul _).symm
    _ ≤ prefixSum (fun n => if Even n then (1 : ℝ) else 0) n := by
        unfold prefixSum
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        intro j _ _
        exact hnonneg j

/-! ## A `{0,1}` stream with density in `(0,1)` is not eventually constant -/

/-- The plain average of an eventually constant `{0,1}` stream tends to its eventual value.
Source: none: infrastructure (witness)
Kind: L
Fidelity: n/a -/
lemma tendsto_average_of_eventuallyConst {x : ℕ → Bool} {N : ℕ} {b : Bool}
    (hb : ∀ n ≥ N, x n = b) :
    Tendsto (weightedAverage (fun _ => (1 : ℝ)) (truthR x)) atTop (𝓝 (if b then 1 else 0)) := by
  set q : ℝ := if b then 1 else 0 with hq
  set C : ℝ := ∑ j ∈ Finset.range N, truthR x j with hC
  have hform : ∀ n ≥ N, weightedAverage (fun _ => (1 : ℝ)) (truthR x) n =
      q + (C - (N : ℝ) * q) / ((n : ℝ) + 1) := by
    intro n hn
    have hden : prefixSum (fun _ => (1 : ℝ)) n ≠ 0 := by
      rw [prefixSum_const_one]; positivity
    rw [weightedAverage_eq_div hden, prefixSum_const_one]
    have hnum : prefixSum (fun i => (1 : ℝ) * truthR x i) n = C + ((n : ℝ) + 1 - N) * q := by
      unfold prefixSum
      simp only [one_mul]
      rw [← Finset.sum_range_add_sum_Ico _ (show N ≤ n + 1 by omega)]
      have htail : ∑ j ∈ Finset.Ico N (n + 1), truthR x j = ∑ j ∈ Finset.Ico N (n + 1), q := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_Ico] at hj
        rw [hq]
        unfold truthR
        rw [hb j hj.1]
      rw [htail, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hnum]
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    field_simp
    ring
  have hdiv : Tendsto (fun n : ℕ => (C - (N : ℝ) * q) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (C - (N : ℝ) * q)).comp
      (tendsto_add_atTop_nat 1)
    refine this.congr (fun n => ?_)
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  have hlim : Tendsto (fun n : ℕ => q + (C - (N : ℝ) * q) / ((n : ℝ) + 1)) atTop (𝓝 (q + 0)) :=
    tendsto_const_nhds.add hdiv
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (hform n hn).symm

/-- **A `{0,1}` stream whose plain average tends to `p ∈ (0,1)` is not eventually constant.**
Source: mandate T1/T6 (non-vacuity)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem not_eventuallyConst_of_average {x : ℕ → Bool} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h : weightedAverage (fun _ => (1 : ℝ)) (truthR x) ≈ₙ (fun _ => p)) :
    ¬ ∃ N b, ∀ n ≥ N, x n = b := by
  rintro ⟨N, b, hb⟩
  have hlim := tendsto_average_of_eventuallyConst hb
  have hlim' : Tendsto (weightedAverage (fun _ => (1 : ℝ)) (truthR x)) atTop (𝓝 p) := by
    have := (h : Tendsto (fun n => weightedAverage (fun _ => (1 : ℝ)) (truthR x) n - p)
      atTop (𝓝 0)).add_const p
    simpa using this
  have := tendsto_nhds_unique hlim hlim'
  cases b <;> simp at this <;> linarith

/-! ## T1 witnesses -/

/-- **T1 is non-degenerate.** For any rule family with `R 0 = constRule` and `p ∈ (0,1)`, the
diagonal sequence is not eventually constant (its density is `p`).
Source: mandate T1 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem diag_not_eventuallyConst (R : ℕ → CausalRule) (hR : R 0 = constRule) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    ¬ ∃ N b, ∀ n ≥ N, diag R (fun _ => p) n = b := by
  apply not_eventuallyConst_of_average hp0 hp1
  have h := diag_pseudorandom_const R p ⟨hp0.le, hp1.le⟩ 0
    (by rw [hR]; exact tendsto_prefixSum_const_one)
  rw [hR] at h
  exact h

/-- **T1 on a second rule.** With `R 1 = evenRule`, the density of `diag R p` on the even days is
also `p`.
Source: mandate T1 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem diag_even_density (R : ℕ → CausalRule) (hR : R 1 = evenRule) {p : ℝ}
    (hp : 0 ≤ p ∧ p ≤ 1) :
    weightedAverage (fun n => if Even n then (1 : ℝ) else 0) (truthR (diag R (fun _ => p))) ≈ₙ
      (fun _ => p) := by
  have h := diag_pseudorandom_const R p hp 1 (by rw [hR]; exact tendsto_prefixSum_evenInd)
  rw [hR] at h
  exact h

/-! ## Numerical sanity: the first two values at `p = 1/2` over the constant rules -/

/-- At `p = 1/2` over constant rules, day `0` is a tie (both continuations have potential
`2 · mass 0`), so `diag` chooses `false`.
Source: mandate T1 (witness, numerical sanity)
Kind: L
Fidelity: n/a -/
theorem diag_const_half_zero : diag (fun _ => constRule) (fun _ => (1 / 2 : ℝ)) 0 = false := by
  unfold diag diagStep
  rw [decide_eq_false]
  intro h
  simp only [pot, mart, factor, constRule, truthR, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.Ico_zero_eq_range, Finset.prod_range_succ, Finset.prod_range_zero, diagPrefix,
    Function.update_self] at h
  ring_nf at h
  linarith

/-- At `p = 1/2` over constant rules, day `1` compensates day `0`: `true` gives potential
`mass 0 · 2 (1 − tilt 0² / 4) + 2 mass 1`, `false` gives `mass 0 · (2 + tilt 0² / 2) + 2 mass 1`,
so `diag` chooses `true`.
Source: mandate T1 (witness, numerical sanity)
Kind: L
Fidelity: n/a -/
theorem diag_const_half_one : diag (fun _ => constRule) (fun _ => (1 / 2 : ℝ)) 1 = true := by
  have h0 : diagPrefix (fun _ => constRule) (fun _ => (1 / 2 : ℝ)) 1 = fun _ => false := by
    funext j
    simp only [diagPrefix]
    by_cases hj : j = 0
    · subst hj
      rw [Function.update_self]
      exact diag_const_half_zero
    · rw [Function.update_of_ne hj]
  unfold diag diagStep
  rw [h0, decide_eq_true]
  simp only [pot, mart, factor, constRule, truthR, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.Ico_zero_eq_range, Finset.prod_range_succ, Finset.prod_range_zero,
    Finset.prod_Ico_succ_top (le_refl 1), Finset.Ico_self, Finset.prod_empty,
    Function.update_self, Function.update_of_ne (show (0 : ℕ) ≠ 1 by norm_num),
    Bool.false_eq_true, if_false, if_true]
  have ht := tilt_pos 0
  have hm := mass_pos 0
  nlinarith [mul_pos hm (mul_pos ht ht)]

/-! ## T4 witness -/

/-- The constant `1` feature progression is P-generable (FAF's `constantRatFeature_generated`).
Source: FAF `AffineCombination.constantRatFeature_generated`
Kind: L
Fidelity: n/a -/
lemma constOne_pgenerable (P : History) :
    PGenerableWeighting (AffineCombination.constantRatFeature 1) :=
  (AffineCombination.constantRatFeature_generated P 1).toWeighting

/-- The constant `1` feature progression denotes `1` everywhere.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma constOne_denote (P : History) :
    (fun i => (AffineCombination.constantRatFeature 1 i).denote P) = fun _ => (1 : ℝ) := by
  funext i
  simp [AffineCombination.constantRatFeature, EF.denote]

/-- The constant `1` feature progression is a divergent weighting on every history.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma constOne_divergent (P : History) :
    DivergentWeighting (AffineCombination.constantRatFeature 1) P := by
  refine ⟨fun n => ?_, ?_⟩
  · simp [AffineCombination.constantRatFeature, EF.denote]
  · rw [constOne_denote]
    exact tendsto_prefixSum_const_one

/-- The plain average of a stream pseudorandom (paper form) on `P` with frequency `p` tends to `p`.
Source: none: infrastructure (witness)
Kind: L
Fidelity: n/a -/
lemma average_of_pseudorandom_all {x : ℕ → Bool} {P : History} {p : ℝ}
    (h : ∀ W : ℕ → EF, PGenerableWeighting W → DivergentWeighting W P →
      weightedAverage (fun i => (W i).denote P) (truthR x) ≈ₙ (fun _ => p)) :
    weightedAverage (fun _ => (1 : ℝ)) (truthR x) ≈ₙ (fun _ => p) := by
  have := h _ (constOne_pgenerable P) (constOne_divergent P)
  rw [constOne_denote] at this
  exact this

/-- **T4 is non-degenerate, over every history.** For any history `P` and `p ∈ (0,1)`, the
fixed-history family over `P` is not eventually constant (its plain density is `p`, through the
constant P-generable weighting, divergent on every history). Repair round 1: generalized from
`P ≡ 1/2` (a trivial market, [[STANDARDS]] §3) to all `P`; the real-market instance is
`diagBuilder_liaHistory_not_eventuallyConst` below.
Source: mandate T4 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem diagBuilder_history_not_eventuallyConst (P : History) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) :
    ¬ ∃ N b, ∀ n ≥ N, diagBuilder (fun _ => P) genWeighting (fun _ => p) n = b :=
  not_eventuallyConst_of_average hp0 hp1 (average_of_pseudorandom_all
    (diagBuilder_pseudorandom_of_history P genWeighting genWeighting_covers p ⟨hp0.le, hp1.le⟩))

/-- **T4's witness over a real market.** With `P := liaHistory (atomDP a y g)` — the LIA over the
process deciding some *fixed* family `y` — the fixed-history family over `P` is not eventually
constant. This inhabits T4's package with a genuine inductor construction rather than a constant
market (round-1 adversarial audit, B2).
Source: mandate T4 (witness); [[STANDARDS]] §3 (not a trivial market)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem diagBuilder_liaHistory_not_eventuallyConst (a g : ℕ → ℕ) (y : ℕ → Bool) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    ¬ ∃ N b, ∀ n ≥ N,
      diagBuilder (fun _ => liaHistory (atomDP a y g)) genWeighting (fun _ => p) n = b :=
  diagBuilder_history_not_eventuallyConst _ hp0 hp1

/-! ## T5 witness: a toy causal builder -/

/-- The toy builder: day `m ≥ 1` prices every sentence at the truth value of member `m − 1`; day
`0` prices at `1/2`.
Source: mandate T5 (witness)
Kind: D
Fidelity: n/a -/
noncomputable def toyBuilder (x : ℕ → Bool) : History :=
  fun m _ => if m = 0 then (1 / 2 : ℝ) else truthR x (m - 1)

/-- The toy builder is causal for delay `n + 1`.
Source: mandate T5 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem toyBuilder_causal : CausalBuilder toyBuilder (fun j => j + 1) := by
  intro x y n h m hm φ
  unfold toyBuilder
  split_ifs with hm0
  · rfl
  · exact truthR_congr (h (m - 1) (by show m - 1 + 1 ≤ n; omega))

/-- The toy builder is not a constant market: it separates the all-`true` and all-`false` streams.
Source: mandate T5 (witness)
Kind: N+
Fidelity: n/a -/
theorem toyBuilder_nonconst : toyBuilder (fun _ => true) ≠ toyBuilder (fun _ => false) := by
  intro h
  have := congrFun (congrFun h 1) ⊤
  simp [toyBuilder, truthR] at this

/-- **T5 on the toy builder**: the diagonal family is pseudorandom relative to the toy market it
builds, for every `f`.
Source: mandate T5 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem toyBuilder_pseudorandom (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    ∀ f : DeferralFunction,
      PseudorandomFrequency (truthR (diagBuilder toyBuilder genWeighting (fun _ => p))) p f
        (toyBuilder (diagBuilder toyBuilder genWeighting (fun _ => p))) :=
  pseudorandomFrequency_of_causal toyBuilder (fun j => j + 1) toyBuilder_causal
    (fun j => Nat.lt_succ_self j) genWeighting genWeighting_covers p hp

/-! ## T6 witnesses -/

/-- **The family of record is non-degenerate.** For `p ∈ (0,1)` and any strict delay `g`,
`truthStar a g p` is not eventually constant: its density on the LIA's constant weighting is `p`.
Source: mandate T6.3 (non-vacuity)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem truthStar_not_eventuallyConst (a g : ℕ → ℕ) (hg : ∀ j, j < g j) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) : ¬ ∃ N b, ∀ n ≥ N, truthStar a g p n = b :=
  not_eventuallyConst_of_average hp0 hp1
    (average_of_pseudorandom_all (truthStar_pseudorandom_all a g hg p ⟨hp0.le, hp1.le⟩))

/-- Literals of distinct members are distinct when `a` is injective.
Source: none: infrastructure (witness)
Kind: L
Fidelity: n/a -/
lemma literalOf_injective {a : ℕ → ℕ} (ha : Function.Injective a) (x : ℕ → Bool) :
    Function.Injective (literalOf a x) := by
  intro j j' h
  unfold literalOf at h
  by_cases hj : x j = true <;> by_cases hj' : x j' = true
  · rw [if_pos hj, if_pos hj'] at h
    exact ha (LO.Propositional.Formula.atom.inj h)
  · rw [if_pos hj, if_neg hj'] at h
    exact absurd h.symm (neg_atom_ne_atom _ _)
  · rw [if_neg hj, if_pos hj'] at h
    exact absurd h (neg_atom_ne_atom _ _)
  · rw [if_neg hj, if_neg hj'] at h
    have h' : LO.Propositional.Formula.imp (LO.Propositional.Formula.atom (a j))
        LO.Propositional.Formula.falsum =
        LO.Propositional.Formula.imp (LO.Propositional.Formula.atom (a j'))
        LO.Propositional.Formula.falsum := h
    exact ha (LO.Propositional.Formula.atom.inj (LO.Propositional.Formula.imp.inj h').1)

/-- **The process of record is not trivial**: every stage of `atomDP a x g` is strictly contained
in a later stage (the literal of member `n + 1` is absent from stage `n` and present from stage
`g (n + 1)`), so the stages grow without bound.
Source: mandate T6.3 (non-vacuity of the process)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem atomDP_stage_ssubset {a : ℕ → ℕ} (ha : Function.Injective a) (x : ℕ → Bool)
    {g : ℕ → ℕ} (hg : ∀ j, j < g j) (n : ℕ) :
    (atomDP a x g).D n ⊂ (atomDP a x g).D (max n (g (n + 1))) := by
  rw [Finset.ssubset_iff_of_subset ((atomDP a x g).mono_le (le_max_left _ _))]
  refine ⟨literalOf a x (n + 1), literalOf_mem_atomDP hg (le_max_right _ _), ?_⟩
  intro hmem
  obtain ⟨j, ⟨hjn, _⟩, hlit⟩ := mem_atomDP_iff.1 hmem
  have := literalOf_injective ha x hlit
  omega

/-! ## T1 witness: an adaptive (stream-reading) rule

`constRule` and `evenRule` are functions of the day alone. `prevRule` reads the stream — weight
`1` on day `n ≥ 1` iff the previous day's truth value is `true` — so it exercises the adaptive
clause of `CausalRule` (strict causality is the content of T1). Adopted from the round-1
adversarial audit's probe `UnionAndAdaptive.lean` §2. -/

/-- Weight `1` on day `n ≥ 1` iff the previous day's truth value is `true`; `0` on day `0`.
Strictly causal (day `n` reads day `n − 1` only) and stream-reading.
Source: mandate T1 (witness); round-1 adversarial audit, item 2
Kind: D
Fidelity: n/a -/
noncomputable def prevRule : CausalRule where
  w x n := if n = 0 then 0 else (if x (n - 1) then 1 else 0)
  nonneg _ n := by split_ifs <;> norm_num
  le_one _ n := by split_ifs <;> norm_num
  causal x y n h := by
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, if_false]
      rw [h (n - 1) (by omega)]

/-- `prevRule` at day `m + 1` reads day `m`.
Source: none: infrastructure (witness)
Kind: L
Fidelity: n/a -/
lemma prevRule_w_succ (x : ℕ → Bool) (m : ℕ) :
    prevRule.w x (m + 1) = if x m then 1 else 0 := by
  simp [prevRule]

/-- A stream that is not eventually constant is `true` infinitely often.
Source: none: infrastructure (witness)
Kind: L
Fidelity: n/a -/
lemma frequently_true_of_not_eventuallyConst {x : ℕ → Bool}
    (h : ¬ ∃ N b, ∀ n ≥ N, x n = b) : ∀ N, ∃ m ≥ N, x m = true := by
  intro N
  by_contra hc
  push Not at hc
  exact h ⟨N, false, fun n hn => by simpa using hc n hn⟩

/-- `prefixSum` at `m + 1` adds the `(m + 1)`-st term.
Source: none: infrastructure (witness)
Kind: L
Fidelity: n/a -/
lemma prefixSum_succ' (w : ℕ → ℝ) (m : ℕ) : prefixSum w (m + 1) = prefixSum w m + w (m + 1) := by
  unfold prefixSum
  rw [Finset.sum_range_succ]

/-- The realized sum of `prevRule` on a stream with infinitely many `true`s diverges.
Source: none: infrastructure (witness)
Kind: L
Fidelity: n/a -/
lemma tendsto_prefixSum_prevRule {x : ℕ → Bool} (hx : ∀ N, ∃ m ≥ N, x m = true) :
    Tendsto (prefixSum (prevRule.w x)) atTop atTop := by
  have hnn : ∀ j, 0 ≤ prevRule.w x j := fun j => prevRule.nonneg x j
  have hstep : ∀ K : ℕ, ∃ n, (K : ℝ) ≤ prefixSum (prevRule.w x) n := by
    intro K
    induction K with
    | zero =>
      refine ⟨0, ?_⟩
      simp only [Nat.cast_zero]
      unfold prefixSum
      exact Finset.sum_nonneg (fun j _ => hnn j)
    | succ K ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m, hmn, hm⟩ := hx n
      refine ⟨m + 1, ?_⟩
      rw [prefixSum_succ', prevRule_w_succ, if_pos hm]
      have hmono := prefixSum_mono_of_nonneg hnn hmn
      push_cast
      linarith
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨n, hn⟩ := hstep ⌈b⌉₊
  refine ⟨n, fun n' hn' => ?_⟩
  calc b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
    _ ≤ prefixSum (prevRule.w x) n := hn
    _ ≤ prefixSum (prevRule.w x) n' := prefixSum_mono_of_nonneg hnn hn'

/-- **T1 on an adaptive rule.** With `R 0 = constRule`, `R 1 = prevRule` and `p ∈ (0,1)`: on the
diagonal, `prevRule`'s realized sum diverges (the diagonal is `true` infinitely often) and the
truth frequency over the days that follow a `true` day tends to `p`. So the hypothesis package of
`diag_pseudorandom_const` at `k = 1` is inhabited by a stream-reading rule: N+ for the adaptive
clause of T1.
Source: mandate T1 (witness); round-1 adversarial audit, item 2
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem diag_prev_density (R : ℕ → CausalRule) (hR0 : R 0 = constRule) (hR1 : R 1 = prevRule)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (prefixSum (prevRule.w (diag R (fun _ => p)))) atTop atTop ∧
    weightedAverage (prevRule.w (diag R (fun _ => p))) (truthR (diag R (fun _ => p))) ≈ₙ
      (fun _ => p) := by
  have hinf := frequently_true_of_not_eventuallyConst (diag_not_eventuallyConst R hR0 hp0 hp1)
  have hdiv := tendsto_prefixSum_prevRule hinf
  refine ⟨hdiv, ?_⟩
  have h := diag_pseudorandom_const R p ⟨hp0.le, hp1.le⟩ 1 (by rw [hR1]; exact hdiv)
  rw [hR1] at h
  exact h

/-! ## T9 witness: the two-family stream of record is not eventually constant -/

/-- The plain average of a stream with values in `[lo, hi]` stays in `[lo, hi]`.
Source: none: infrastructure (witness); FAF `weightedAverage_mem_Icc`
Kind: L
Fidelity: n/a -/
lemma average_mem_Icc_of_mem {q : ℕ → ℝ} {lo hi : ℝ} (hq : ∀ n, lo ≤ q n ∧ q n ≤ hi) (n : ℕ) :
    weightedAverage (fun _ => (1 : ℝ)) q n ∈ Set.Icc lo hi :=
  weightedAverage_mem_Icc (fun _ => zero_le_one) (fun i => ⟨(hq i).1, (hq i).2⟩)
    (by rw [prefixSum_const_one]; positivity)

/-- **A `{0,1}` stream whose plain average of `truthR x − q` tends to `0`, for a target `q` with
values in `[lo, hi] ⊂ (0,1)`, is not eventually constant.** (If it were eventually `b`, the plain
average of `q` would tend to `b ∈ {0,1}`, but it lives in `[lo, hi]`.)
Source: mandate T9 (non-vacuity); round-1 fidelity audit, item 5
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem not_eventuallyConst_of_varied_average {x : ℕ → Bool} {q : ℕ → ℝ} {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : hi < 1) (hq : ∀ n, lo ≤ q n ∧ q n ≤ hi)
    (h : weightedAverage (fun _ => (1 : ℝ)) (fun j => truthR x j - q j) ≈ₙ (fun _ => 0)) :
    ¬ ∃ N b, ∀ n ≥ N, x n = b := by
  rintro ⟨N, b, hb⟩
  have hx := tendsto_average_of_eventuallyConst hb
  have h0 : Tendsto (weightedAverage (fun _ => (1 : ℝ)) (fun j => truthR x j - q j)) atTop
      (𝓝 0) := by
    have h' := h
    unfold AsympEq at h'
    simpa only [sub_zero] using h'
  have hq' : Tendsto (weightedAverage (fun _ => (1 : ℝ)) q) atTop (𝓝 (if b then 1 else 0)) := by
    have := hx.sub h0
    rw [sub_zero] at this
    refine this.congr (fun n => ?_)
    have hden : prefixSum (fun _ => (1 : ℝ)) n ≠ 0 := by
      rw [prefixSum_const_one]; positivity
    rw [weightedAverage_sub _ _ _ hden]
    ring
  have hlo' : lo ≤ (if b then 1 else 0) :=
    ge_of_tendsto' hq' (fun n => (average_mem_Icc_of_mem hq n).1)
  have hhi' : (if b then 1 else 0) ≤ hi :=
    le_of_tendsto' hq' (fun n => (average_mem_Icc_of_mem hq n).2)
  cases b <;> simp at hlo' hhi' <;> linarith

/-- **The two-family stream of record is non-degenerate.** For `p₁, p₂ ∈ (0,1)` and any strict
delay `g`, `truthStar₂ a g p₁ p₂` is not eventually constant: through the constant P-generable
weighting on the LIA of record, the plain average of `truthR − pairTarget` tends to `0`.
Source: mandate T9 (non-vacuity); round-1 fidelity audit, item 5
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem truthStar₂_not_eventuallyConst (a g : ℕ → ℕ) (hg : ∀ j, j < g j) {p₁ p₂ : ℚ}
    (h₁ : 0 < p₁ ∧ p₁ < 1) (h₂ : 0 < p₂ ∧ p₂ < 1) :
    ¬ ∃ N b, ∀ n ≥ N, truthStar₂ a g p₁ p₂ n = b := by
  have hv := truthStar₂_variedPseudorandom a g hg p₁ p₂ ⟨h₁.1.le, h₁.2.le⟩ ⟨h₂.1.le, h₂.2.le⟩
    succDeferral
  have hdivg := constOne_divergent (liaHistory (atomDP a (truthStar₂ a g p₁ p₂) g))
  have hpat := deferralPatient_succDeferral_of_divergent hdivg
  have hge := hv.1 _ (constOne_pgenerable (liaHistory (atomDP a (truthStar₂ a g p₁ p₂) g)))
    hdivg hpat
  have hle := hv.2 _ (constOne_pgenerable (liaHistory (atomDP a (truthStar₂ a g p₁ p₂) g)))
    hdivg hpat
  rw [constOne_denote] at hge hle
  have heq := asympEq_iff_asympLE_asympGE.2 ⟨hle, hge⟩
  refine not_eventuallyConst_of_varied_average (q := fun n => (pairTarget p₁ p₂ n : ℝ))
    (lo := min (p₁ : ℝ) p₂) (hi := max (p₁ : ℝ) p₂) ?_ ?_ ?_ heq
  · exact lt_min (by exact_mod_cast h₁.1) (by exact_mod_cast h₂.1)
  · exact max_lt (by exact_mod_cast h₁.2) (by exact_mod_cast h₂.2)
  · intro n
    unfold pairTarget
    split_ifs
    · exact ⟨min_le_left _ _, le_max_left _ _⟩
    · exact ⟨min_le_right _ _, le_max_right _ _⟩

/-! ## The union shape: non-degeneracy -/

/-- **The family inside a union process is non-degenerate.** For `p ∈ (0,1)`, any fixed `DP₀` and
strict delay `g`, `unionStar DP₀ a g p` is not eventually constant (through the constant
P-generable weighting on the LIA over the union).
Source: plan `### li-pseudorandom` (`paperDP T` instance shape); mandate T6.3 (non-vacuity)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem unionStar_not_eventuallyConst (DP₀ : DeductiveProcess) (a g : ℕ → ℕ) (hg : ∀ j, j < g j)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : ¬ ∃ N b, ∀ n ≥ N, unionStar DP₀ a g p n = b :=
  not_eventuallyConst_of_average hp0 hp1
    (average_of_pseudorandom_all (unionStar_pseudorandom_all DP₀ a g hg p ⟨hp0.le, hp1.le⟩))

/-! ## T9 witnesses: the subfamilies are non-degenerate (repair round 2) -/

/-- **The even subfamily of the two-family stream is non-degenerate.** For `p₁ ∈ (0,1)` (and
`p₂ ∈ [0,1]`), the even members of `truthStar₂ a g p₁ p₂` are not eventually constant: through
the constant P-generable weighting on the LIA of record, their plain density is `p₁`.
Source: mandate T9 (non-vacuity); repair round 2
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem truthStar₂_even_not_eventuallyConst (a g : ℕ → ℕ) (hg : ∀ j, j < g j) {p₁ p₂ : ℚ}
    (h₁ : 0 < p₁ ∧ p₁ < 1) (h₂ : 0 ≤ p₂ ∧ p₂ ≤ 1) :
    ¬ ∃ N b, ∀ n ≥ N, truthStar₂ a g p₁ p₂ (2 * n) = b :=
  not_eventuallyConst_of_average (x := fun n => truthStar₂ a g p₁ p₂ (2 * n)) (p := (p₁ : ℝ))
    (by exact_mod_cast h₁.1) (by exact_mod_cast h₁.2)
    (average_of_pseudorandom_all
      (truthStar₂_even_pseudorandom_all a g hg p₁ p₂ ⟨h₁.1.le, h₁.2.le⟩ h₂))

/-- **The odd subfamily of the two-family stream is non-degenerate.** For `p₂ ∈ (0,1)` (and
`p₁ ∈ [0,1]`), the odd members of `truthStar₂ a g p₁ p₂` are not eventually constant.
Source: mandate T9 (non-vacuity); repair round 2
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem truthStar₂_odd_not_eventuallyConst (a g : ℕ → ℕ) (hg : ∀ j, j < g j) {p₁ p₂ : ℚ}
    (h₁ : 0 ≤ p₁ ∧ p₁ ≤ 1) (h₂ : 0 < p₂ ∧ p₂ < 1) :
    ¬ ∃ N b, ∀ n ≥ N, truthStar₂ a g p₁ p₂ (2 * n + 1) = b :=
  not_eventuallyConst_of_average (x := fun n => truthStar₂ a g p₁ p₂ (2 * n + 1)) (p := (p₂ : ℝ))
    (by exact_mod_cast h₂.1) (by exact_mod_cast h₂.2)
    (average_of_pseudorandom_all
      (truthStar₂_odd_pseudorandom_all a g hg p₁ p₂ h₁ ⟨h₂.1.le, h₂.2.le⟩))

/-- **Every family of the countable-family stream is non-degenerate.** For a family `r` with
`q r ∈ (0,1)` (all `q r ∈ [0,1]`), the members of family `r` of `truthStarω a g q` are not
eventually constant.
Source: mandate T9 (non-vacuity, countably many families); repair round 2
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem truthStarω_family_not_eventuallyConst (a g : ℕ → ℕ) (hg : ∀ j, j < g j) (q : ℕ → ℚ)
    (hq : ∀ r, 0 ≤ q r ∧ q r ≤ 1) (r : ℕ) (hr : 0 < q r ∧ q r < 1) :
    ¬ ∃ N b, ∀ m ≥ N, truthStarω a g q (Nat.pair r m) = b :=
  not_eventuallyConst_of_average (x := fun m => truthStarω a g q (Nat.pair r m)) (p := (q r : ℝ))
    (by exact_mod_cast hr.1) (by exact_mod_cast hr.2)
    (average_of_pseudorandom_all (truthStarω_pseudorandom_all a g hg q hq r))

/-! ## The hypotheses are load-bearing (adopted from the round-2 adversarial probe `Vacuity.lean`) -/

/-- The omniscient builder: day `m` prices every sentence at the truth value of member `m` —
the market of the mandate's § Context 1, against which no fixed family is pseudorandom.
Source: mandate § Context 1, T5 trap (i); round-2 adversarial audit, item 6
Kind: D
Fidelity: exact -/
noncomputable def omniscient : (ℕ → Bool) → History := fun x m _ => truthR x m

/-- The omniscient builder is a `CausalBuilder` for the *non-strict* profile `g = id`: without
the strictness `∀ j, j < g j`, T5 would apply to it, and its conclusion is false there.
Source: mandate § Context 1, T5 trap (i); round-2 adversarial audit, item 6
Kind: N+
Fidelity: n/a -/
theorem omniscient_causalBuilder_id : CausalBuilder omniscient id := by
  intro x y n h m hm _
  unfold omniscient
  exact truthR_congr (h m hm)

/-- The omniscient builder is not a `CausalBuilder` for the delay-one profile: day `0` reads
member `0`, which is decided only on day `1`. The strictness hypothesis of T5/T6 excludes it.
Source: mandate § Context 1, T5 trap (i); round-2 adversarial audit, item 6
Kind: N+
Fidelity: n/a -/
theorem omniscient_not_causalBuilder_succ : ¬ CausalBuilder omniscient (fun j => j + 1) := by
  intro h
  have := h (fun _ => true) (fun _ => false) 0 (fun j hj => by simp at hj) 0 le_rfl ⊤
  simp [omniscient, truthR] at this

/-- The trivial enumeration `fun _ _ => EF.const 0` does not cover the P-generable weightings
(the constant-`1` weighting is missed): T5's covering hypothesis `hcov` is not free, and the
package discharges it with `genWeighting_covers`.
Source: mandate T5; round-2 adversarial audit, item 7
Kind: N+
Fidelity: n/a -/
theorem trivial_enumeration_does_not_cover :
    ¬ ∀ W, PGenerableWeighting W → ∃ k, (fun (_ : ℕ) (_ : ℕ) => EF.const 0) k = W := by
  intro h
  obtain ⟨k, hk⟩ := h _
    ((AffineCombination.constantRatFeature_generated (fun _ _ => (0 : ℝ)) 1).toWeighting)
  have h0 := congrFun hk 0
  simp only [AffineCombination.constantRatFeature] at h0
  cases h0

end Cleanroom.Li.LiPseudorandom
