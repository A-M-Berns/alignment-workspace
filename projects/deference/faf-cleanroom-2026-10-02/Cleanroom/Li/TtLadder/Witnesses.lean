import Cleanroom.Li.TtLadder.Averaged
import Cleanroom.Li.TtLadder.Closure
import Mathlib.Analysis.PSeries

/-!
# `tt-ladder`: witnesses I — the harmonic and square gates (W2, W4, creep)

Target 5 of [[tt-ladder-mandate]], the rational-arithmetic witnesses. Default `t = 1/2`,
`δ = 1/10`. Each witness ships its `[0,1]` bounds for **all** `n` (the closure theorems need
them) and is graded in its docstring. Every non-arrow of the Hasse diagram is stated as
`∃ a e, (∀ n, a n ∈ Icc 0 1) ∧ (∀ n, e n ∈ Icc 0 1) ∧ P a e ∧ ¬ Q a e` with the witness named.

* `harmQuote t δ n = t + δ/(n+1)`: the gate is exactly `1/(n+1)` (`gateSeq_harmQuote`) — the
  trust lab's `witness_gate`, which stalled at two `sorry`s there. With `e ≡ 0`: **W4**
  (`L_prod`, divergent gate mass, `¬Avg`, `¬T`), trust-lab-060's parameters (`t = 3/4`,
  `ε = δ = 1/8`, `middle_rung_false`) and root-deference-051's (`t = 1/2`, `ε = 1/4`).
* `sqQuote n = 1/2 + (1/10)/(n+1)²`: the gate is `1/(n+1)²`. With `e ≡ 0`: **W2**
  (`BV`, `T_∀ε`, `L_prod`, `¬L_cond`, and `¬T_full` at `t' = 3/10` — the fixed-`t` artifact).
* `creepE n = 1/2 − 1/(n+2)` under the solid gate `a ≡ 3/5`: **creep** (`L_cond`, `L_prod`,
  `T_∀ε`, `¬BV`, `¬T_full`); and under the harmonic gate: the witness of the averaged lemma's
  full hypothesis package with a non-constant divergent gate (`averaged_package_harmonic_creep`).
* `avgSeq_gatedMeanSeq_vacuous_sqQuote`: on a summable gate the averaged predicates hold
  against every credence — the vacuous end of "conditional on divergent gate mass".
* `prop_a_needs_lower_bound`: with `e` unbounded below, `T_∀ε ∧ ¬L_prod` — so Prop A's `0 ≤ e`
  hypothesis is not decorative.

Over real sequences; nothing here is a theorem about inductors.
-/

namespace Cleanroom.Li.TtLadder

open LogicalInduction Filter Topology Finset
open Cleanroom.Found.LiAsympCalc

/-! ## Series helpers -/

/-- The shifted harmonic series `∑ 1/(n+1)` diverges (Mathlib's `not_summable_one_div_natCast`
through `summable_nat_add_iff`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem not_summable_one_div_succ : ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
  intro h
  apply Real.not_summable_one_div_natCast
  rw [← summable_nat_add_iff 1]
  refine h.congr (fun n => ?_)
  push_cast
  ring

/-- A sequence termwise above `c/(n+1)` for some `c > 0` is not summable.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem not_summable_of_one_div_succ_le {f : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : ∀ n : ℕ, c / ((n : ℝ) + 1) ≤ f n) : ¬ Summable f := by
  intro h
  apply not_summable_one_div_succ
  have h2 : Summable (fun n : ℕ => c / ((n : ℝ) + 1)) :=
    h.of_nonneg_of_le (fun n => show 0 ≤ c / ((n : ℝ) + 1) from
      div_nonneg hc.le (by positivity)) hf
  refine (h2.mul_left (1 / c)).congr (fun n => ?_)
  field_simp

/-- `∑ 1/(n+1)²` converges.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem summable_one_div_succ_sq : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
  refine this.congr (fun n => ?_)
  push_cast
  ring

/-- `1/(n+2) → 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem tendsto_one_div_add_two : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
  have := (tendsto_add_atTop_iff_nat 1).2
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine this.congr (fun n => ?_)
  push_cast
  ring

/-- A summable sequence is eventually below any positive bound (packaging of
`Summable.tendsto_atTop_zero`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem summable_eventually_lt {f : ℕ → ℝ} (h : Summable f) {m : ℝ} (hm : 0 < m) :
    ∀ᶠ n in atTop, f n < m :=
  h.tendsto_atTop_zero.eventually (gt_mem_nhds hm)

/-- The ramp when the gap is nonnegative: `ctsInd δ x y = min 1 ((x - y)/δ)` for `y ≤ x`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem ctsInd_of_le {δ : ℚ} (hδ : 0 < δ) {x y : ℝ} (h : y ≤ x) :
    ctsInd δ x y = min 1 ((x - y) / δ) := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold ctsInd
  rw [max_eq_right (div_nonneg (by linarith) hδR.le)]

/-- The weighted average of the zero sequence is `0` (both branches).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem weightedAverage_zero_right (w : ℕ → ℝ) (n : ℕ) :
    weightedAverage w (fun _ => (0 : ℝ)) n = 0 := by
  unfold weightedAverage
  split_ifs <;> simp [prefixSum]

/-! ## The harmonic gate `harmQuote t δ n = t + δ/(n+1)` -/

/-- The quote `t + δ/(n+1)`, whose gate at `(t, δ)` is exactly `1/(n+1)`.
Source: trust-lab-060 (`wa`); root-deference-051 (flag); lean-deference-2-003 (W4)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def harmQuote (t δ : ℚ) (n : ℕ) : ℝ := t + δ / ((n : ℝ) + 1)

/-- **`witness_gate`** (the trust lab's stalled lemma): `gateSeq t δ (harmQuote t δ) n = 1/(n+1)`
for `δ > 0`.
Source: trust-lab-060 (`witness_gate`, two `sorry`s at `WeakeningLadder.lean:241–242`)
Kind: P
Fidelity: exact (generalised from `t = 3/4, δ = 1/8` to all `t` and `δ > 0`)
Hyps: (a) none -/
theorem gateSeq_harmQuote {t δ : ℚ} (hδ : 0 < δ) (n : ℕ) :
    gateSeq t δ (harmQuote t δ) n = 1 / ((n : ℝ) + 1) := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hdiv : 0 ≤ (δ : ℝ) / ((n : ℝ) + 1) := div_nonneg hδR.le hn.le
  unfold gateSeq harmQuote
  rw [ctsInd_of_le hδ (by linarith)]
  have : ((t : ℝ) + δ / ((n : ℝ) + 1) - t) / δ = 1 / ((n : ℝ) + 1) := by
    field_simp
    ring
  rw [this, min_eq_right]
  rw [div_le_one hn]
  linarith

/-- `harmQuote t δ n ∈ [0,1]` when `0 ≤ t` and `t + δ ≤ 1`.
Source: trust-lab-060 (`wa_bounds`)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem harmQuote_mem_Icc {t δ : ℚ} (hδ : 0 < δ) (ht : (0 : ℝ) ≤ t) (ht1 : (t : ℝ) + δ ≤ 1)
    (n : ℕ) : harmQuote t δ n ∈ Set.Icc (0 : ℝ) 1 := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h1 : (δ : ℝ) / ((n : ℝ) + 1) ≤ δ := div_le_self hδR.le hn
  have h0 : 0 ≤ (δ : ℝ) / ((n : ℝ) + 1) := div_nonneg hδR.le (by linarith)
  unfold harmQuote
  constructor <;> linarith

/-- The gate mass of the harmonic gate diverges: `prefixSum (gateSeq t δ (harmQuote t δ)) → ∞`.
Source: lean-deference-2-003 (W4: `∑ G = ∞`)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem tendsto_prefixSum_gateSeq_harmQuote {t δ : ℚ} (hδ : 0 < δ) :
    Tendsto (prefixSum (gateSeq t δ (harmQuote t δ))) atTop atTop := by
  have h := (tendsto_add_atTop_iff_nat 1).2 Real.tendsto_sum_range_one_div_nat_succ_atTop
  refine h.congr (fun n => ?_)
  unfold prefixSum
  exact Finset.sum_congr rfl (fun i _ => (gateSeq_harmQuote hδ i).symm)

/-- **`L_prod` for the harmonic gate against the parked credence `e ≡ 0`**: the product
`G_n (0 − t) = −t/(n+1) → 0` (for every rational `t`).
Source: lean-deference-2-003 (W4); trust-lab-060 (`q_n → 0`)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem lProdSeq_harmQuote_zero {t δ : ℚ} (hδ : 0 < δ) :
    LProdSeq (harmQuote t δ) (fun _ => 0) t δ := by
  intro η hη
  have hlim : Tendsto (fun n : ℕ => (t : ℝ) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (t : ℝ)
    rwa [mul_zero] at this
  filter_upwards [hlim.eventually (gt_mem_nhds hη)] with n hn
  show (0 : ℝ) ≤ gateSeq t δ (harmQuote t δ) n * (0 - t) + η
  rw [gateSeq_harmQuote hδ]
  have : 1 / ((n : ℝ) + 1) * (0 - t) = -((t : ℝ) * (1 / ((n : ℝ) + 1))) := by ring
  rw [this]
  linarith

/-- The harmonic gate against `e ≡ 0` fails `T(t,ε,δ)` whenever the violation ramp saturates,
`δ ≤ t − ε`: the weight is then exactly `1/(n+1)`.
Source: lean-deference-2-003 (W4); trust-lab-060; root-deference-051
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem not_tSeq_harmQuote_zero {t ε δ : ℚ} (hδ : 0 < δ) (h : (δ : ℝ) ≤ t - ε) :
    ¬ TSeq (harmQuote t δ) (fun _ => 0) t ε δ := by
  unfold TSeq
  refine not_summable_of_one_div_succ_le one_pos (fun n => ?_)
  rw [viol_eq_gateSeq_mul, gateSeq_harmQuote hδ,
    (ctsInd_eq_one_iff hδ _ _).2 (by linarith), mul_one]

/-- The harmonic gate against `e ≡ 0` fails `Avg(t,ε,δ)` when the bound is not vacuous,
`0 < t − ε − δ`: the gate mass diverges and the gated average of `0` is `0`.
Source: lean-deference-2-003 (W4: `¬Avg`); trust-lab-060 (`witness_not_averaged`)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem not_avgSeq_harmQuote_zero {t ε δ : ℚ} (hδ : 0 < δ) (h : (0 : ℝ) < t - ε - δ) :
    ¬ AvgSeq (harmQuote t δ) (fun _ => 0) t ε δ := by
  intro havg
  have h2 := havg (tendsto_prefixSum_gateSeq_harmQuote hδ) (((t : ℝ) - ε - δ) / 2) (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 h2
  have := hN N le_rfl
  rw [weightedAverage_zero_right] at this
  linarith

/-! ### W4: `t = 1/2`, `δ = 1/10` -/

/-- **W4** (`N+`, non-constant quote): `a n = 1/2 + (1/10)/(n+1)`, `e ≡ 0`. `L_prod` holds, the
gate mass diverges, `Avg(1/2, 1/10, 1/10)` fails, `T(1/2, 1/10, 1/10)` fails and (root-deference-051's
instance) `T(1/2, 1/4, 1/10)` fails.
Source: lean-deference-2-003 (W4); root-deference-051 (flag, `t = ½, ε = ¼`)
Kind: N+
Fidelity: exact
Hyps: n/a -/
theorem w4_witness :
    (∀ n, harmQuote (1/2) (1/10) n ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ n, (fun _ : ℕ => (0 : ℝ)) n ∈ Set.Icc (0 : ℝ) 1) ∧
    LProdSeq (harmQuote (1/2) (1/10)) (fun _ => 0) (1/2) (1/10) ∧
    Tendsto (prefixSum (gateSeq (1/2) (1/10) (harmQuote (1/2) (1/10)))) atTop atTop ∧
    ¬ AvgSeq (harmQuote (1/2) (1/10)) (fun _ => 0) (1/2) (1/10) (1/10) ∧
    ¬ TSeq (harmQuote (1/2) (1/10)) (fun _ => 0) (1/2) (1/10) (1/10) ∧
    ¬ TSeq (harmQuote (1/2) (1/10)) (fun _ => 0) (1/2) (1/4) (1/10) :=
  ⟨harmQuote_mem_Icc (by norm_num) (by norm_num) (by norm_num),
    fun _ => ⟨le_rfl, zero_le_one⟩,
    lProdSeq_harmQuote_zero (by norm_num),
    tendsto_prefixSum_gateSeq_harmQuote (by norm_num),
    not_avgSeq_harmQuote_zero (by norm_num) (by norm_num),
    not_tSeq_harmQuote_zero (by norm_num) (by norm_num),
    not_tSeq_harmQuote_zero (by norm_num) (by norm_num)⟩

/-- **Non-arrow `L_prod ⇏ T(t,ε,δ)`** at `t = 1/2, ε = δ = 1/10` (W4; W1 in `WitnessesLog.lean`
is the chat's own witness).
Source: lean-deference-2-002 ("`L_prod ⇏ T(t,ε)` (W1)"); trust-lab-060
Kind: N+
Fidelity: variant: sequence-level
Hyps: n/a -/
theorem lProdSeq_not_tSeq :
    ∃ a e : ℕ → ℝ, (∀ n, a n ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ n, e n ∈ Set.Icc (0 : ℝ) 1) ∧
      LProdSeq a e (1/2) (1/10) ∧ ¬ TSeq a e (1/2) (1/10) (1/10) :=
  ⟨_, _, w4_witness.1, w4_witness.2.1, w4_witness.2.2.1, w4_witness.2.2.2.2.2.1⟩

/-- **Non-arrow `L_prod ⇏ Avg(t,ε,δ)`** at `t = 1/2, ε = δ = 1/10` (W4): the "limit"
configuration sits below *both* rungs the printed ladder places under it.
Source: lean-deference-2-002 ("`L_prod ⇏ Avg` (W4)"); trust-lab-060
Kind: N+
Fidelity: variant: sequence-level
Hyps: n/a -/
theorem lProdSeq_not_avgSeq :
    ∃ a e : ℕ → ℝ, (∀ n, a n ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ n, e n ∈ Set.Icc (0 : ℝ) 1) ∧
      LProdSeq a e (1/2) (1/10) ∧ ¬ AvgSeq a e (1/2) (1/10) (1/10) :=
  ⟨_, _, w4_witness.1, w4_witness.2.1, w4_witness.2.2.1, w4_witness.2.2.2.2.1⟩

/-- **Refutation of `li-deference` l.243–245** ("`q_n ≳ₙ 0 ⟹ ∑ w_n < ∞`") at root-deference-051's
own parameters `t = ½, ε = ¼, δ = 1/10`, `a n = t + δ/(n+1)`, `e ≡ 0`: the implication
`L_prod ⇒ T(t,ε,δ)` fails for `[0,1]`-valued sequences. Reading of the note's sentence:
`LProdSeq a e t δ → TSeq a e t ε δ` for all `a, e` (ATTRIBUTION-UNVETTED as the note's intent;
the pasted commentary l.263–272 reads it the same way). Survivor: the arrow under
`SupportNondegenerate` (`Repair.lean`).
Source: [[li-deference]] l.243–245; root-deference-051 (flag); root-deference-2-006
Kind: P
Fidelity: variant: sequence-level (negation of the note's sequence claim)
Hyps: (a) none -/
theorem not_forall_lProdSeq_imp_tSeq :
    ¬ ∀ a e : ℕ → ℝ, (∀ n, a n ∈ Set.Icc (0 : ℝ) 1) → (∀ n, e n ∈ Set.Icc (0 : ℝ) 1) →
      LProdSeq a e (1/2) (1/10) → TSeq a e (1/2) (1/4) (1/10) := by
  intro h
  exact w4_witness.2.2.2.2.2.2
    (h _ _ w4_witness.1 w4_witness.2.1 w4_witness.2.2.1)

/-! ### The trust lab's parameters: `t = 3/4`, `ε = δ = 1/8` -/

/-- **`witness_gate`** at the trust lab's own parameters: the gate of `3/4 + (1/8)/(n+1)` at
`(3/4, 1/8)` is `1/(n+1)` — the lemma `WeakeningLadder.lean` left at two `sorry`s.
Source: trust-lab-060 (`witness_gate`)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem witness_gate (n : ℕ) :
    gateSeq (3/4) (1/8) (harmQuote (3/4) (1/8)) n = 1 / ((n : ℝ) + 1) :=
  gateSeq_harmQuote (by norm_num) n

/-- **`middle_rung_false`** (trust-lab-060, never compiled there): at `t = 3/4`, `ε = δ = 1/8`,
"limit ⇒ bounded-ε-violation" fails for `[0,1]`-valued sequences — the harmonic gate damps
the product while the weight `1/(n+1)` diverges. Reading of `faithful-acceleration` l.128–130's
second `⇓`: `LProdSeq a e t δ → TSeq a e t ε δ` (ATTRIBUTION-UNVETTED). Survivor:
`Repair.lean`.
Source: trust-lab-060 (`middle_rung_false`); [[faithful-acceleration]] l.124–134 (second `⇓`); [[scout-acceleration]] Finding B
Kind: P
Fidelity: variant: sequence-level (negation of the note's sequence claim)
Hyps: (a) none -/
theorem middle_rung_false :
    ¬ ∀ a e : ℕ → ℝ, (∀ n, a n ∈ Set.Icc (0 : ℝ) 1) → (∀ n, e n ∈ Set.Icc (0 : ℝ) 1) →
      LProdSeq a e (3/4) (1/8) → TSeq a e (3/4) (1/8) (1/8) := by
  intro h
  exact not_tSeq_harmQuote_zero (t := 3/4) (ε := 1/8) (δ := 1/8) (by norm_num) (by norm_num)
    (h _ _ (harmQuote_mem_Icc (by norm_num) (by norm_num) (by norm_num))
      (fun _ => ⟨le_rfl, zero_le_one⟩) (lProdSeq_harmQuote_zero (by norm_num)))

/-- **`witness_not_averaged`** (trust-lab-060): the same configuration fails the averaged rung
at `t = 3/4`, `ε = δ = 1/8` (gated average `0 < 1/2`).
Source: trust-lab-060 (`witness_not_averaged`)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem witness_not_averaged :
    ¬ AvgSeq (harmQuote (3/4) (1/8)) (fun _ => 0) (3/4) (1/8) (1/8) :=
  not_avgSeq_harmQuote_zero (by norm_num) (by norm_num)

/-! ## The square gate `sqQuote n = 1/2 + (1/10)/(n+1)²` (W2) -/

/-- The quote `1/2 + (1/10)/(n+1)²`, whose gate at `(1/2, 1/10)` is `1/(n+1)²`.
Source: lean-deference-2-003 (W2)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def sqQuote (n : ℕ) : ℝ := 1/2 + (1/10) / ((n : ℝ) + 1) ^ 2

/-- `gateSeq (1/2) (1/10) sqQuote n = 1/(n+1)²`.
Source: lean-deference-2-003 (W2)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem gateSeq_sqQuote (n : ℕ) : gateSeq (1/2) (1/10) sqQuote n = 1 / ((n : ℝ) + 1) ^ 2 := by
  have hn : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  have hdiv : 0 ≤ (1/10 : ℝ) / ((n : ℝ) + 1) ^ 2 := by positivity
  unfold gateSeq sqQuote
  rw [ctsInd_of_le (by norm_num) (by push_cast; linarith)]
  have : ((1/2 : ℝ) + (1/10) / ((n : ℝ) + 1) ^ 2 - ((1/2 : ℚ) : ℝ)) / ((1/10 : ℚ) : ℝ) =
      1 / ((n : ℝ) + 1) ^ 2 := by
    push_cast
    field_simp
    ring
  rw [this, min_eq_right]
  rw [div_le_one hn]
  have : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  nlinarith

/-- `sqQuote n ∈ [1/2, 3/5] ⊆ [0,1]`.
Source: lean-deference-2-003 (W2)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem sqQuote_bounds (n : ℕ) : 1/2 ≤ sqQuote n ∧ sqQuote n ≤ 3/5 := by
  have hn : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have h1 : (1/10 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 1/10 := div_le_self (by norm_num) hn
  have h0 : 0 ≤ (1/10 : ℝ) / ((n : ℝ) + 1) ^ 2 := by positivity
  unfold sqQuote
  constructor <;> linarith

/-- `sqQuote n ∈ [0,1]`.
Source: lean-deference-2-003 (W2)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem sqQuote_mem_Icc (n : ℕ) : sqQuote n ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨by linarith [(sqQuote_bounds n).1], by linarith [(sqQuote_bounds n).2]⟩

/-- **W2, `BV`**: `BV(1/2, 1/10)` for `sqQuote` against `e ≡ 0` — the weight is `1/(n+1)²`.
Source: lean-deference-2-003 (W2)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem bvSeq_sqQuote_zero : BVSeq sqQuote (fun _ => 0) (1/2) (1/10) := by
  unfold BVSeq
  refine summable_one_div_succ_sq.congr (fun n => ?_)
  rw [gateSeq_sqQuote, (ctsInd_eq_one_iff (by norm_num) _ _).2 (by norm_num), mul_one]

/-- **W2, `¬L_cond`**: the gate is touched every day (`a n > 1/2`) while `e ≡ 0`, so at the margin
`c = 1/4` no day is admissible.
Source: lean-deference-2-003 (W2)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem not_lCondSeq_sqQuote_zero : ¬ LCondSeq sqQuote (fun _ => 0) (1/2) := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h (1/4) (by norm_num))
  have hg : ((1/2 : ℚ) : ℝ) < sqQuote N := by
    have := (sqQuote_bounds N).1
    have h0 : (0 : ℝ) < (1/10) / ((N : ℝ) + 1) ^ 2 := by positivity
    unfold sqQuote at *
    push_cast
    linarith
  have := hN N le_rfl hg
  norm_num at this

/-- **W2, `¬T_full`** (the fixed-`t` artifact's numeric half): at `t' = 3/10`, `ε = 1/10`, the
same quotes make the gate solid (`a n ≥ 1/2 = t' + 2δ`) and the weight is identically `1`.
Source: lean-deference-2-005; lean-deference-2-003 (W2, "at any `t' < t`")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem not_tFullSeq_sqQuote_zero : ¬ TFullSeq sqQuote (fun _ => 0) (1/10) := by
  intro h
  have hs := h (3/10) (1/10) (by norm_num)
  unfold TSeq at hs
  refine not_summable_of_one_div_succ_le one_pos (fun n => ?_) hs
  rw [viol_eq_gateSeq_mul]
  unfold gateSeq
  rw [(ctsInd_eq_one_iff (by norm_num) _ _).2 (by linarith [(sqQuote_bounds n).1]),
    (ctsInd_eq_one_iff (by norm_num) _ _).2 (by norm_num), one_mul]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [div_le_one (by linarith)]
  linarith

/-- **W2** (`N+`, non-constant quote): `a n = 1/2 + (1/10)/(n+1)²`, `e ≡ 0`: `BV`, `T_∀ε` and
`L_prod` hold at `t = 1/2`, `L_cond(1/2)` fails, and `T_full(1/10)` fails.
Source: lean-deference-2-003 (W2); lean-deference-2-005
Kind: N+
Fidelity: exact
Hyps: n/a -/
theorem w2_witness :
    (∀ n, sqQuote n ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ n, (fun _ : ℕ => (0 : ℝ)) n ∈ Set.Icc (0 : ℝ) 1) ∧
    BVSeq sqQuote (fun _ => 0) (1/2) (1/10) ∧
    TAllEpsSeq sqQuote (fun _ => 0) (1/2) (1/10) ∧
    LProdSeq sqQuote (fun _ => 0) (1/2) (1/10) ∧
    ¬ LCondSeq sqQuote (fun _ => 0) (1/2) ∧
    ¬ TFullSeq sqQuote (fun _ => 0) (1/10) :=
  ⟨sqQuote_mem_Icc, fun _ => ⟨le_rfl, zero_le_one⟩, bvSeq_sqQuote_zero,
    tAllEpsSeq_of_bvSeq (by norm_num) bvSeq_sqQuote_zero,
    lProdSeq_of_bvSeq (by norm_num) (fun _ => le_rfl) bvSeq_sqQuote_zero,
    not_lCondSeq_sqQuote_zero, not_tFullSeq_sqQuote_zero⟩

/-- **Non-arrows `T_∀ε ⇏ L_cond`, `BV ⇏ L_cond`** at `t = 1/2, δ = 1/10` (W2): the top arrow
of the printed ladder is *false* under the conditional reading.
Source: lean-deference-2-002 ("`T_∀ε ⇏ L_cond` (W2); `BV ⇏ L_cond` (W2)"); root-fa-007 (flag)
Kind: N+
Fidelity: variant: sequence-level
Hyps: n/a -/
theorem tAllEpsSeq_bvSeq_not_lCondSeq :
    ∃ a e : ℕ → ℝ, (∀ n, a n ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ n, e n ∈ Set.Icc (0 : ℝ) 1) ∧
      TAllEpsSeq a e (1/2) (1/10) ∧ BVSeq a e (1/2) (1/10) ∧ ¬ LCondSeq a e (1/2) :=
  ⟨_, _, w2_witness.1, w2_witness.2.1, w2_witness.2.2.2.1, w2_witness.2.2.1,
    w2_witness.2.2.2.2.2.1⟩

/-- **The fixed-`t` artifact, satisfiable side**: `T_∀ε(t₀) ∧ ¬L_cond(t₀) ∧ ¬T_full` is
satisfiable (W2 at `t₀ = 1/2`). Read beside `lCondSeq_of_tFullSeq` (`Closure.lean`): the
escape lives at one threshold and closes under the theorem's `∀ t`.
Source: lean-deference-2-005 (C6 true at fixed `t`, false for `T_full`)
Kind: N+
Fidelity: variant: sequence-level
Hyps: n/a -/
theorem tAllEpsSeq_not_lCondSeq_not_tFullSeq :
    ∃ a e : ℕ → ℝ, (∀ n, a n ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ n, e n ∈ Set.Icc (0 : ℝ) 1) ∧
      TAllEpsSeq a e (1/2) (1/10) ∧ ¬ LCondSeq a e (1/2) ∧ ¬ TFullSeq a e (1/10) :=
  ⟨_, _, w2_witness.1, w2_witness.2.1, w2_witness.2.2.2.1, w2_witness.2.2.2.2.2.1,
    w2_witness.2.2.2.2.2.2⟩

/-- **The averaged predicates are vacuous on a summable gate**: W2's quote (gate `1/(n+1)²`,
summable mass) satisfies `GatedMean(1/2)` and `Avg(1/2, ε, 1/10)` against *every* credence —
including `e ≡ 0`, a credence that is `0` on every flagged day. This is what "conditional on
divergent gate mass" in the `AvgSeq`/`GatedMeanSeq` docstrings means; every `Avg ∧ ¬T` witness
of this package has divergent mass because `¬T` forces it (the weight is `≤` the gate).
Source: [[tt-ladder-audit-r1-adversarial]] N-c (probe A3); [[tt-ladder-mandate]] target 1 (`AvgSeq`: "harmless under the antecedent — say so")
Kind: N−
Fidelity: variant: sequence-level (the degenerate end of the definition, on record)
Hyps: n/a -/
theorem avgSeq_gatedMeanSeq_vacuous_sqQuote (e : ℕ → ℝ) (ε : ℚ) :
    GatedMeanSeq sqQuote e (1/2) (1/10) ∧ AvgSeq sqQuote e (1/2) ε (1/10) := by
  have hs : Summable (gateSeq (1/2) (1/10) sqQuote) :=
    summable_one_div_succ_sq.congr (fun n => (gateSeq_sqQuote n).symm)
  have hndiv : ¬ Tendsto (prefixSum (gateSeq (1/2) (1/10) sqQuote)) atTop atTop := by
    intro h
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (h.eventually (eventually_gt_atTop (∑' n, gateSeq (1/2) (1/10) sqQuote n)))
    have h1 := hN N le_rfl
    have h2 : prefixSum (gateSeq (1/2) (1/10) sqQuote) N ≤ ∑' n, gateSeq (1/2) (1/10) sqQuote n :=
      hs.sum_le_tsum _ (fun i _ => gateSeq_nonneg _ _ _ _)
    linarith
  exact ⟨fun h => absurd h hndiv, fun h => absurd h hndiv⟩

/-! ## Creep: `e n = 1/2 − 1/(n+2)` under the solid gate `a ≡ 3/5` -/

/-- The creeping credence `1/2 − 1/(n+2)` (indexed through `n + 2` so it is `≥ 0` on every day;
the sources' `t − 1/n` from `n ≥ 2`).
Source: trust-lab-062 (creep); root-fa-007 (`e_n − t = −1/n`); root-deference-2-006 (ii)
Kind: D
Fidelity: variant: reindexed by `n + 2`
Hyps: n/a -/
noncomputable def creepE (n : ℕ) : ℝ := 1/2 - 1 / ((n : ℝ) + 2)

/-- `creepE n ∈ [0, 1/2]`.
Source: trust-lab-062
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem creepE_bounds (n : ℕ) : 0 ≤ creepE n ∧ creepE n ≤ 1/2 := by
  have hn : (2 : ℝ) ≤ (n : ℝ) + 2 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h1 : 1 / ((n : ℝ) + 2) ≤ 1/2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have h0 : 0 ≤ 1 / ((n : ℝ) + 2) := by positivity
  unfold creepE
  constructor <;> linarith

/-- The solid gate: `gateSeq (1/2) (1/10) (fun _ => 3/5) n = 1`.
Source: trust-lab-062 (`g ≡ 1`)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem gateSeq_const_three_fifths (n : ℕ) : gateSeq (1/2) (1/10) (fun _ => 3/5) n = 1 :=
  (ctsInd_eq_one_iff (by norm_num) _ _).2 (by norm_num)

/-- **Creep, `L_cond`**: `1/2 − 1/(n+2)` is eventually above `1/2 − c` for every `c > 0`.
Source: trust-lab-062 (creep: "limit holds"); root-deference-2-006 (ii)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem lCondSeq_creep : LCondSeq (fun _ => 3/5) creepE (1/2) := by
  intro c hc
  filter_upwards [tendsto_one_div_add_two.eventually (gt_mem_nhds hc)] with n hn _
  unfold creepE
  push_cast
  linarith

/-- **Creep, `¬BV`**: the margin-free weight `min 1 (10/(n+2))` is `≥ (1/2)/(n+1)` — harmonic.
Source: trust-lab-062 (creep: "margin-free count diverges"); root-deference-2-006 (ii); root-fa-007
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem not_bvSeq_creep : ¬ BVSeq (fun _ => 3/5) creepE (1/2) (1/10) := by
  unfold BVSeq
  refine not_summable_of_one_div_succ_le (c := 1/2) (by norm_num) (fun n => ?_)
  rw [gateSeq_const_three_fifths, one_mul]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [ctsInd_of_le (by norm_num) (by linarith [(creepE_bounds n).2])]
  refine le_min ?_ ?_
  · rw [div_le_one (by linarith)]; linarith
  · unfold creepE
    push_cast
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by linarith
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    rw [div_le_iff₀ h1]
    have hid : ((1/2 : ℝ) - (1/2 - 1 / ((n : ℝ) + 2))) / (1/10) * ((n : ℝ) + 1) =
        10 * (((n : ℝ) + 1) / ((n : ℝ) + 2)) := by
      field_simp
      try ring
    rw [hid]
    have : (1/2 : ℝ) ≤ ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
      rw [le_div_iff₀ h2]; linarith
    linarith

/-- **Creep, `¬T_full`**: `e` never dominates `a ≡ 3/5` (`liminf (e − a) = −1/10`).
Source: lean-deference-2-003 (W3's `¬T_full`, `liminf(e − a) = −δ`)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem not_tFullSeq_creep : ¬ TFullSeq (fun _ => 3/5) creepE (1/10) := by
  intro h
  have hdom := dominates_of_tFullSeq (fun _ => ⟨by norm_num, by norm_num⟩) (by norm_num) h
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hdom (1/20) (by norm_num))
  have := hN N le_rfl
  have := (creepE_bounds N).2
  linarith

/-- **Creep** (`N+`, non-constant credence, rational arithmetic): `a ≡ 3/5`, `e n = 1/2 − 1/(n+2)`:
`L_cond`, `L_prod`, `T_∀ε` hold at `t = 1/2, δ = 1/10`; `BV` fails; `T_full(1/10)` fails.
Source: trust-lab-062 (creep); root-deference-2-006 (ii); root-fa-007
Kind: N+
Fidelity: exact
Hyps: n/a -/
theorem creep_witness :
    (∀ n, (fun _ : ℕ => (3/5 : ℝ)) n ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ n, creepE n ∈ Set.Icc (0 : ℝ) 1) ∧
    LCondSeq (fun _ => 3/5) creepE (1/2) ∧
    LProdSeq (fun _ => 3/5) creepE (1/2) (1/10) ∧
    TAllEpsSeq (fun _ => 3/5) creepE (1/2) (1/10) ∧
    ¬ BVSeq (fun _ => 3/5) creepE (1/2) (1/10) ∧
    ¬ TFullSeq (fun _ => 3/5) creepE (1/10) :=
  ⟨fun _ => ⟨by norm_num, by norm_num⟩,
    fun n => ⟨(creepE_bounds n).1, by linarith [(creepE_bounds n).2]⟩,
    lCondSeq_creep, lProdSeq_of_lCondSeq (by norm_num) lCondSeq_creep,
    tAllEpsSeq_of_lCondSeq (by norm_num) lCondSeq_creep, not_bvSeq_creep, not_tFullSeq_creep⟩

/-- **Non-arrows `L_prod ⇏ BV`, `L_cond ⇏ BV`, `T_∀ε ⇏ BV`** at `t = 1/2, δ = 1/10` (creep):
the top rung of the printed ladder is strictly above the limit rung, and `BV` and `L_cond` are
incomparable (with `tAllEpsSeq_bvSeq_not_lCondSeq`).
Source: lean-deference-2-002 (W3's role); trust-lab-062; root-fa-007
Kind: N+
Fidelity: variant: sequence-level
Hyps: n/a -/
theorem lProdSeq_lCondSeq_tAllEpsSeq_not_bvSeq :
    ∃ a e : ℕ → ℝ, (∀ n, a n ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ n, e n ∈ Set.Icc (0 : ℝ) 1) ∧
      LProdSeq a e (1/2) (1/10) ∧ LCondSeq a e (1/2) ∧ TAllEpsSeq a e (1/2) (1/10) ∧
      ¬ BVSeq a e (1/2) (1/10) :=
  ⟨_, _, creep_witness.1, creep_witness.2.1, creep_witness.2.2.2.1, creep_witness.2.2.1,
    creep_witness.2.2.2.2.1, creep_witness.2.2.2.2.2.1⟩

/-! ## The averaged lemma's full package: creep under the harmonic gate -/

/-- The margin-`1/10` violation ramp of the creeping credence at `t = 1/2` is `0` from day `8`
on (`creepE n ≥ 2/5` iff `n ≥ 8`).
Source: none: infrastructure (for the averaged-lemma package witnesses)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem ctsInd_creepE_eventually_zero {n : ℕ} (hn : 8 ≤ n) :
    ctsInd (1/10) (((1/2 : ℚ) : ℝ) - ((1/10 : ℚ) : ℝ)) (creepE n) = 0 := by
  refine (ctsInd_eq_zero_iff (by norm_num) _ _).2 ?_
  unfold creepE
  push_cast
  have h8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have : 1 / ((n : ℝ) + 2) ≤ 1 / 10 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  linarith

/-- Under *any* gate `g`, the margin-`1/10` weight `g_n · Ind_{1/10}(creepE n < 2/5)` is summable:
it has finitely many nonzero terms (`ctsInd_creepE_eventually_zero`).
Source: none: infrastructure (for the averaged-lemma package witnesses)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem summable_mul_ramp_creepE (g : ℕ → ℝ) :
    Summable (fun n => g n * ctsInd (1/10) (((1/2 : ℚ) : ℝ) - ((1/10 : ℚ) : ℝ)) (creepE n)) := by
  refine summable_of_ne_finset_zero (s := Finset.range 8) (fun n hn => ?_)
  have hn8 : 8 ≤ n := not_lt.1 (fun h' => hn (Finset.mem_range.2 h'))
  show g n * ctsInd (1/10) (((1/2 : ℚ) : ℝ) - ((1/10 : ℚ) : ℝ)) (creepE n) = 0
  rw [ctsInd_creepE_eventually_zero hn8, mul_zero]

/-- **Witness of the averaged lemma's full package with a non-constant, divergent gate**
(`N+`, both sequences non-constant): the harmonic gate `1/(n+1)` (from `harmQuote (1/2) (1/10)`)
against the creeping credence `creepE n = 1/2 − 1/(n+2)`, at `t = 1/2`, `ε = δ = 1/10`. Every
hypothesis of `averaged_of_summable` is inhabited — gate in `[0,1]`, credence `≥ 0`, gate mass
divergent (`tendsto_prefixSum_gateSeq_harmQuote`), margin weight summable (it is `0` from day
`8`) — and the lemma's conclusion, the gated average `≳ₙ 3/10`, follows. This is the mandate's
"`g n = 1/(n+1)`, divergent, so the `weightedAverage` denominator is exercised".
Source: [[tt-ladder-mandate]] target 4 ("Witness for the lemma's full package (`N+`) … one with non-constant `g`"); root-fa-006
Kind: N+
Fidelity: variant: sequence-level
Hyps: n/a -/
theorem averaged_package_harmonic_creep :
    (∀ n, gateSeq (1/2) (1/10) (harmQuote (1/2) (1/10)) n ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ n, 0 ≤ creepE n) ∧
    Tendsto (prefixSum (gateSeq (1/2) (1/10) (harmQuote (1/2) (1/10)))) atTop atTop ∧
    Summable (fun n => gateSeq (1/2) (1/10) (harmQuote (1/2) (1/10)) n *
      ctsInd (1/10) (((1/2 : ℚ) : ℝ) - ((1/10 : ℚ) : ℝ)) (creepE n)) ∧
    AsympGE (weightedAverage (gateSeq (1/2) (1/10) (harmQuote (1/2) (1/10))) creepE)
      (fun _ => ((1/2 : ℚ) : ℝ) - ((1/10 : ℚ) : ℝ) - ((1/10 : ℚ) : ℝ)) := by
  have hg : ∀ n, gateSeq (1/2) (1/10) (harmQuote (1/2) (1/10)) n ∈ Set.Icc (0 : ℝ) 1 :=
    gateSeq_mem_Icc _ _ _
  have he : ∀ n, 0 ≤ creepE n := fun n => (creepE_bounds n).1
  have hdiv : Tendsto (prefixSum (gateSeq (1/2) (1/10) (harmQuote (1/2) (1/10)))) atTop atTop :=
    tendsto_prefixSum_gateSeq_harmQuote (by norm_num)
  have hs := summable_mul_ramp_creepE (gateSeq (1/2) (1/10) (harmQuote (1/2) (1/10)))
  exact ⟨hg, he, hdiv, hs, averaged_of_summable (by norm_num) hg he hdiv hs⟩

/-- The same pair in the ladder's own predicates: `harmQuote (1/2) (1/10)` against `creepE`
satisfies `T(1/2, 1/10, 1/10)` and `Avg(1/2, 1/10, 1/10)` — the arrow `T ⇒ Avg` inhabited by a
non-constant quote and a non-constant credence with divergent gate mass.
Source: [[tt-ladder-mandate]] target 4; root-fa-006
Kind: N+
Fidelity: variant: sequence-level
Hyps: n/a -/
theorem tSeq_avgSeq_harmQuote_creep :
    TSeq (harmQuote (1/2) (1/10)) creepE (1/2) (1/10) (1/10) ∧
    AvgSeq (harmQuote (1/2) (1/10)) creepE (1/2) (1/10) (1/10) :=
  ⟨summable_mul_ramp_creepE _,
    avgSeq_of_tSeq (by norm_num) (fun n => (creepE_bounds n).1) (summable_mul_ramp_creepE _)⟩

/-! ## Prop A needs a lower bound on `e` -/

/-- `sqQuote` against the unbounded credence `e n = −(n+1)²` has `T_∀ε(1/2, 1/10)`: every
weight is `≤ 1/(n+1)²`.
Source: none: infrastructure (the `T_∀ε` half of `prop_a_needs_lower_bound`)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem tAllEpsSeq_sqQuote_neg_sq :
    TAllEpsSeq sqQuote (fun n => -((n : ℝ) + 1) ^ 2) (1/2) (1/10) := by
  intro ε hε
  unfold TSeq
  refine summable_one_div_succ_sq.of_nonneg_of_le (fun n => viol_nonneg _ _ _ _ _ _)
    (fun n => ?_)
  rw [viol_eq_gateSeq_mul, gateSeq_sqQuote]
  exact mul_le_of_le_one_right (by positivity) (ctsInd_le_one _ _ _)

/-- `sqQuote` against the unbounded credence `e n = −(n+1)²` fails `L_prod(1/2, 1/10)`:
`G_n (e_n − t) = −1 − (1/2)/(n+1)² ≤ −1` on every day.
Source: none: infrastructure (the `¬L_prod` half of `prop_a_needs_lower_bound`)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem not_lProdSeq_sqQuote_neg_sq :
    ¬ LProdSeq sqQuote (fun n => -((n : ℝ) + 1) ^ 2) (1/2) (1/10) := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h (1/2) (by norm_num))
  have := hN N le_rfl
  have h1 : (0 : ℝ) ≤ gateSeq (1/2) (1/10) sqQuote N * (-((N : ℝ) + 1) ^ 2 - ((1/2 : ℚ) : ℝ))
      + 1/2 := this
  rw [gateSeq_sqQuote] at h1
  have hn : (0 : ℝ) < ((N : ℝ) + 1) ^ 2 := by positivity
  have : 1 / ((N : ℝ) + 1) ^ 2 * (-((N : ℝ) + 1) ^ 2 - ((1/2 : ℚ) : ℝ)) =
      -1 - (1/2) / ((N : ℝ) + 1) ^ 2 := by
    push_cast
    field_simp
    try ring
  rw [this] at h1
  have : 0 ≤ (1/2 : ℝ) / ((N : ℝ) + 1) ^ 2 := by positivity
  linarith

/-- **Prop A's lower bound is necessary**: with `a = sqQuote` (gate `1/(n+1)²`) and the
unbounded credence `e n = −(n+1)²`, every violation weight is summable (it is `≤ 1/(n+1)²`)
while `G_n (e_n − t) ≤ −1` on every day, so `L_prod` fails. The `[0,1]` bound on `e` in the
sources' standing assumptions is doing real work in `T_∀ε ⇒ L_prod`; the mandate's "the
`[0,1]` bounds only where stated" would have let this slip. The same pair also has
`BV(1/2, 1/10)` (`bvSeq_needs_lower_bound`, `Bounds.lean`), so `BV ⇒ L_prod` needs the bound too.
Source: [[tt-ladder-mandate]] target 2 (iv) (finding); lean-deference-046 Prop A
Kind: N+
Fidelity: n/a (a counterexample to the unbounded form)
Hyps: n/a -/
theorem prop_a_needs_lower_bound :
    ∃ a e : ℕ → ℝ, (∀ n, a n ∈ Set.Icc (0 : ℝ) 1) ∧
      TAllEpsSeq a e (1/2) (1/10) ∧ ¬ LProdSeq a e (1/2) (1/10) :=
  ⟨sqQuote, fun n => -((n : ℝ) + 1) ^ 2, sqQuote_mem_Icc, tAllEpsSeq_sqQuote_neg_sq,
    not_lProdSeq_sqQuote_neg_sq⟩

end Cleanroom.Li.TtLadder
