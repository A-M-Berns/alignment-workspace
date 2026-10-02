import Cleanroom.Fa.FaDelayBsi.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# `fa-delay-bsi` · Split (T2, T3(i)): Theorem C's per-day inequality, with the right case split

BSI §5's "split": on any day, `w ≤ w^{frozen} + (2/ε)·|c − F|` (lean-deference-055, root-fa-029,
vq-wiki-039 (b)). BSI splits on the *frozen credence* against the threshold `t − ε/2` and claims
`w^{frozen} ≥` a fixed fraction of `w` in the first case — false (`bsi_split_wrong_threshold`
below: `w = 1`, `w^{frozen} = 1/K` for every `K`); [[delay-and-visibility]] §5 and
[[delay-program]] T6 repair the threshold to `t − ε/2 − δ` ("the ramp saturated"). Neither split
is the right one: the inequality holds by splitting on the **ramp values** `θ := Ind_δ(c < t−ε)`
against `η := Ind_δ(F < t−ε/2)`, with **no relation between `δ` and `ε`** —
`violWeight_le_frozen_add_displacement`. The case `θ > η` forces `F − c > ε/2` by comparing the
ramp arguments, so the displacement term alone exceeds `1 ≥ w`.

The refined form `violWeight_le_frozen_mul_live_add_displacement` keeps the frozen term only on
days that are *current* violations (`c < t − ε`): that is the quantity the v3 trader can bound
(T3 shows the plain frozen sum is not finite), and the shape the OPEN summed bound needs.

Kind `P` (real content: the case analysis), sequence-level (FAF's `ctsInd`). Not `theoremC`.
-/

namespace Cleanroom.Fa.FaDelayBsi

open LogicalInduction Cleanroom.Found.LiAsympCalc
open Finset

/-! ## A. Two ramp facts -/

/-- A ramp is at most its (clipped-below) argument: `ctsInd δ x y ≤ max 0 ((x − y)/δ)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem ctsInd_le_max (δ : ℚ) (x y : ℝ) : ctsInd δ x y ≤ max 0 ((x - y) / (δ : ℝ)) :=
  min_le_right _ _

/-- A ramp strictly below `1` is at least its argument: `ctsInd δ x y < 1 → (x − y)/δ ≤ ctsInd δ x y`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem div_le_ctsInd_of_lt_one {δ : ℚ} {x y : ℝ} (h : ctsInd δ x y < 1) :
    (x - y) / (δ : ℝ) ≤ ctsInd δ x y := by
  unfold ctsInd at h ⊢
  have hmax : max 0 ((x - y) / (δ : ℝ)) < 1 := by
    by_contra hc
    rw [not_lt] at hc
    have := min_eq_left hc
    rw [this] at h
    exact lt_irrefl _ h
  rw [min_eq_right hmax.le]
  exact le_max_right _ _

/-! ## B. T2: the split inequality -/

/-- **T2 (headline). Theorem C's per-day split inequality, with the right case split.** For
rationals `t`, `ε > 0`, `δ > 0` and reals `a` (quote), `c` (live credence), `F` (frozen credence):
`violWeight t ε δ a c ≤ frozenWeight t ε δ a F + (2/ε) · |c − F|`.
Proof: with `q := Ind_δ(a > t)`, `θ := Ind_δ(c < t − ε)`, `η := Ind_δ(F < t − ε/2)`: if `θ ≤ η`
then `qθ ≤ qη`; if `θ > η` then `θ > 0` gives `c < t − ε`, `η < 1` gives
`(t − ε/2 − F)/δ ≤ η < θ ≤ (t − ε − c)/δ`, so `F − c > ε/2` and `(2/ε)|c − F| > 1 ≥ qθ`.
**No relation between `δ` and `ε` is needed**, and the split is on the ramp values, not on `F`
against any threshold (BSI's split at `t − ε/2` is false as a case analysis,
`bsi_split_wrong_threshold`; the sources diagnose the saturation point `t − ε/2 − δ` and verify
the displayed inequality separately — formalizer's observation, not the sources' claim: a case
split *at* `t − ε/2 − δ` would give only the displacement `ε/2 − δ` and the constant `2/(ε − 2δ)`).
Scope: sequence-level (FAF's `ctsInd`); one day.
Source: BSI §5 line 98 ("The split"; lean-deference-055, lean-deference-054); [[delay-program]] §6 T6 line 258 (root-fa-029: "BSI's case split is stated at the wrong threshold … but the displayed inequality is nonetheless valid"); [[delay-and-visibility]] §5 (vq-wiki-039 (b)); [[fa-delay-bsi-mandate]] T2 route
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem violWeight_le_frozen_add_displacement {t ε δ : ℚ} (hε : 0 < ε) (hδ : 0 < δ)
    (a c F : ℝ) :
    violWeight t ε δ a c ≤ frozenWeight t ε δ a F + (2 / (ε : ℝ)) * |c - F| := by
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold violWeight frozenWeight
  set q := ctsInd δ a (t : ℝ) with hq
  set θ := ctsInd δ ((t : ℝ) - ε) c with hθ
  set η := ctsInd δ ((t : ℝ) - ε / 2) F with hη
  have hq01 := ctsInd_mem_Icc δ a (t : ℝ)
  have hθ01 := ctsInd_mem_Icc δ ((t : ℝ) - ε) c
  have hη01 := ctsInd_mem_Icc δ ((t : ℝ) - ε / 2) F
  have hdisp : 0 ≤ (2 / (ε : ℝ)) * |c - F| := by positivity
  rcases le_or_gt θ η with hle | hlt
  · -- `θ ≤ η`: the frozen term dominates
    have : q * θ ≤ q * η := mul_le_mul_of_nonneg_left hle hq01.1
    linarith
  · -- `θ > η`: the displacement exceeds `ε/2`, so the displacement term exceeds `1 ≥ qθ`
    have hθpos : 0 < θ := lt_of_le_of_lt hη01.1 hlt
    have hc : c < (t : ℝ) - ε := (ctsInd_pos_iff hδ _ _).1 hθpos
    have hηlt : η < 1 := lt_of_lt_of_le hlt hθ01.2
    have h1 : ((t : ℝ) - ε / 2 - F) / (δ : ℝ) ≤ η := div_le_ctsInd_of_lt_one hηlt
    have h2 : θ ≤ ((t : ℝ) - ε - c) / (δ : ℝ) := by
      have := ctsInd_le_max δ ((t : ℝ) - ε) c
      rw [max_eq_right (div_nonneg (by linarith) hδR.le)] at this
      exact this
    have h3 : ((t : ℝ) - ε / 2 - F) / (δ : ℝ) < ((t : ℝ) - ε - c) / (δ : ℝ) := by
      linarith
    have h4 : (t : ℝ) - ε / 2 - F < (t : ℝ) - ε - c :=
      (div_lt_div_iff_of_pos_right hδR).1 h3
    have h5 : (ε : ℝ) / 2 < |c - F| := by
      rw [abs_sub_comm]
      exact lt_of_lt_of_le (by linarith) (le_abs_self _)
    have h6 : (1 : ℝ) < (2 / (ε : ℝ)) * |c - F| := by
      have : (2 / (ε : ℝ)) * ((ε : ℝ) / 2) = 1 := by field_simp
      calc (1 : ℝ) = (2 / (ε : ℝ)) * ((ε : ℝ) / 2) := this.symm
        _ < (2 / (ε : ℝ)) * |c - F| :=
            mul_lt_mul_of_pos_left h5 (by positivity)
    have hqθ : q * θ ≤ 1 := mul_le_one₀ hq01.2 hθ01.1 hθ01.2
    have hqη : 0 ≤ q * η := mul_nonneg hq01.1 hη01.1
    linarith

/-- **T2, refined (stronger than BSI's display).** The frozen term is needed only on days that are
*current* violations (`c < t − ε`):
`violWeight ≤ frozenWeight · 𝟙[c < t − ε] + (2/ε) · |c − F|`. Same case split; in the case
`θ ≤ η` a positive `violWeight` forces `c < t − ε`. This is the quantity the v3 trader can bound
(it buys the current question at its *live* price on fired current-violation days), and T3 shows
the plain frozen sum cannot be bounded; the OPEN summed bound (`Open.lean`) is stated from this
form.
Scope: sequence-level (FAF's `ctsInd`); one day.
Source: BSI §5 line 100 ("for frozen-gated days that are not current violations the trader's same-day check … declines the trade, and the declined mass is again dominated by displacement"); [[delay-program]] §6 T6 (root-fa-029)
Kind: P
Fidelity: stronger: the frozen term carries the current-violation indicator
Hyps: (a) none -/
theorem violWeight_le_frozen_mul_live_add_displacement {t ε δ : ℚ} (hε : 0 < ε) (hδ : 0 < δ)
    (a c F : ℝ) :
    violWeight t ε δ a c ≤
      frozenWeight t ε δ a F * (if c < (t : ℝ) - ε then (1 : ℝ) else 0) +
        (2 / (ε : ℝ)) * |c - F| := by
  by_cases hc : c < (t : ℝ) - ε
  · rw [if_pos hc, mul_one]
    exact violWeight_le_frozen_add_displacement hε hδ a c F
  · rw [if_neg hc, mul_zero, zero_add]
    have : violWeight t ε δ a c = 0 := by
      unfold violWeight
      rw [(ctsInd_eq_zero_iff hδ _ _).2 (not_lt.1 hc), mul_zero]
    rw [this]
    positivity

/-! ## C. The finding: BSI's case split is at the wrong threshold (and the repair is not needed) -/

/-- **W2 (finding, T2). BSI's split is false as a case analysis.** For any `t`, `ε > 0`, `δ > 0`
with `t + δ ≤ 1` and `0 ≤ t − ε − δ`, and any `K ≥ 1`: at `a = 1`, `c = 0`,
`F = t − ε/2 − δ/K` the frozen credence is below BSI's threshold `t − ε/2`, yet `violWeight = 1`
and `frozenWeight = 1/K`. So "frozen credence below `t − ε/2` ⟹ `w^{frozen} ≥` a fixed fraction of
`w`" (BSI §5 line 98) fails for every fraction. BSI's constants `(3/16, 1/32, 1/32)`, `K = 100`
are an instance (`bsi_split_wrong_threshold_bsi`).
Scope: sequence-level (FAF's `ctsInd`); one day.
Source: BSI §5 line 98; [[fa-delay-bsi-mandate]] T2 finding (i)
Kind: N+
Fidelity: exact (the witness inhabits the full hypothesis package of T2 and refutes BSI's case clause)
Hyps: (a) none -/
theorem bsi_split_wrong_threshold {t ε δ : ℚ} (hε : 0 < ε) (hδ : 0 < δ) (ht1 : t + δ ≤ 1)
    (ht0 : 0 ≤ t - ε - δ) (K : ℕ) (hK : 1 ≤ K) :
    let F : ℝ := (t : ℝ) - ε / 2 - δ / K
    F < (t : ℝ) - ε / 2 ∧ violWeight t ε δ 1 0 = 1 ∧ frozenWeight t ε δ 1 F = 1 / K := by
  intro F
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have ht1R : (t : ℝ) + δ ≤ 1 := by exact_mod_cast ht1
  have ht0R : (0 : ℝ) ≤ t - ε - δ := by exact_mod_cast ht0
  refine ⟨?_, ?_, ?_⟩
  · show (t : ℝ) - ε / 2 - δ / K < (t : ℝ) - ε / 2
    have : (0 : ℝ) < δ / K := div_pos hδR hKR
    linarith
  · exact (violWeight_eq_one_iff hδ t ε 1 0).2 ⟨ht1R, by linarith⟩
  · unfold frozenWeight
    rw [(ctsInd_eq_one_iff hδ _ _).2 (by linarith), one_mul]
    unfold ctsInd
    have harg : ((t : ℝ) - ε / 2 - F) / (δ : ℝ) = 1 / K := by
      show ((t : ℝ) - ε / 2 - ((t : ℝ) - ε / 2 - δ / K)) / (δ : ℝ) = 1 / K
      field_simp
      ring
    rw [harg, max_eq_right (by positivity), min_eq_right (by
      rw [div_le_one hKR]; exact hK1)]

/-- BSI's own constants: at `(t, ε, δ) = (3/16, 1/32, 1/32)` and `F = t − ε/2 − δ/100`, `c = 0`,
`a = 1`: `w = 1`, `w^{frozen} = 1/100`.
Source: BSI §4 (the constants), §5 line 98; [[fa-delay-bsi-mandate]] W2
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem bsi_split_wrong_threshold_bsi :
    violWeight (3 / 16) (1 / 32) (1 / 32) 1 0 = 1 ∧
      frozenWeight (3 / 16) (1 / 32) (1 / 32) 1
        (((3 / 16 : ℚ) : ℝ) - ((1 / 32 : ℚ) : ℝ) / 2 - ((1 / 32 : ℚ) : ℝ) / (100 : ℕ)) = 1 / 100 := by
  have h := bsi_split_wrong_threshold (t := 3 / 16) (ε := 1 / 32) (δ := 1 / 32) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) 100 (by norm_num)
  simp only at h
  exact ⟨h.2.1, by rw [h.2.2]; norm_num⟩

/-! ## D. BSI Lemma 4's constants (supporting lemmas; the theorem they serve is refuted) -/

/-- **BSI Lemma 4, quote ramp** (supporting lemma for a refuted theorem; no ledger row). At
`t = 3/16`, `δ = 1/32`: a quote within `1/64` of `¼` clears the threshold by a full `δ`, so the
quote ramp equals `1`. Over FAF's `ctsInd`, replacing `Staleness.lean`'s `softInd`
(lean-deference-030); the theorem it served, BSI Theorem B, is refuted (T1, `Locality.lean`).
Source: BSI §4 Lemma 4 (lean-deference-030); `research/lean-deference/Staleness.lean:181`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem bsi_quote_ramp {q : ℝ} (h : |q - 1 / 4| ≤ 1 / 64) :
    ctsInd (1 / 32) q ((3 / 16 : ℚ) : ℝ) = 1 := by
  refine (ctsInd_eq_one_iff (by norm_num) _ _).2 ?_
  have := (abs_le.1 h).1
  push_cast
  linarith

/-- **BSI Lemma 4, credence ramp** (supporting lemma for a refuted theorem; no ledger row). At
`t − ε = 5/32`, `δ = 1/32`: a credence within `1/64` of `0` leaves the threshold by a full `δ`, so
the credence ramp equals `1`.
Source: BSI §4 Lemma 4 (lean-deference-030); `Staleness.lean:188`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem bsi_credence_ramp {p : ℝ} (h : |p| ≤ 1 / 64) :
    ctsInd (1 / 32) (((3 / 16 : ℚ) : ℝ) - ((1 / 32 : ℚ) : ℝ)) p = 1 := by
  refine (ctsInd_eq_one_iff (by norm_num) _ _).2 ?_
  have := (abs_le.1 h).2
  push_cast
  linarith

/-- **BSI Lemma 4's two margin inequalities**, as bare arithmetic: `1/4 − 1/64 > 3/16 + 1/32` and
`1/64 < 5/32 − 1/32`. Supporting lemma for a refuted theorem; no ledger row.
Source: BSI §4 Lemma 4 (lean-deference-030); `Staleness.lean:196`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem bsi_lemma4_margins :
    (1 : ℝ) / 4 - 1 / 64 > 3 / 16 + 1 / 32 ∧ (1 : ℝ) / 64 < 5 / 32 - 1 / 32 := by
  constructor <;> norm_num

/-- With BSI Lemma 4's two margins, the day's violation weight at BSI's constants is `1`: both
ramps saturate. (The *conclusion* of Lemma 4, as ramp arithmetic; the hypotheses — quote near
`¼`, credence near `0` — are what Lemma 3 was to supply and cannot, T1.)
Source: BSI §4 Lemma 4 (lean-deference-030)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem bsi_lemma4_weight {q p : ℝ} (hq : |q - 1 / 4| ≤ 1 / 64) (hp : |p| ≤ 1 / 64) :
    violWeight (3 / 16) (1 / 32) (1 / 32) q p = 1 := by
  unfold violWeight
  rw [bsi_quote_ramp hq, bsi_credence_ramp hp, one_mul]

/-! ## E. T3(i): the finite-sum form along any schedule -/

/-- **T3(i). The finite-sum split along any schedule `d`** (sequences `a`, `c`, `F`; `K` terms):
`∑_{k<K} w_{d_k} ≤ ∑_{k<K} w^{frozen}_{d_k} + (2/ε) ∑_{k<K} |c_{d_k} − F_{d_k}|`. Term-by-term from T2.
Scope: sequence-level (FAF's `ctsInd`); any index map `d`.
Source: BSI §5 Theorem C first display (lean-deference-054); [[delay-program]] §6 T6
Kind: L
Fidelity: exact (BSI's first display, finite sums)
Hyps: (a) none -/
theorem sum_violWeight_le {t ε δ : ℚ} (hε : 0 < ε) (hδ : 0 < δ) (a c F : ℕ → ℝ) (d : ℕ → ℕ)
    (K : ℕ) :
    ∑ k ∈ range K, violWeight t ε δ (a (d k)) (c (d k)) ≤
      ∑ k ∈ range K, frozenWeight t ε δ (a (d k)) (F (d k)) +
        (2 / (ε : ℝ)) * ∑ k ∈ range K, |c (d k) - F (d k)| := by
  rw [mul_sum, ← sum_add_distrib]
  exact sum_le_sum fun k _ => violWeight_le_frozen_add_displacement hε hδ _ _ _

/-- **T3(i), refined**: the frozen term restricted to current-violation days.
Scope: sequence-level (FAF's `ctsInd`); any index map `d`.
Source: BSI §5 line 100; [[delay-program]] §6 T6
Kind: L
Fidelity: stronger: as `violWeight_le_frozen_mul_live_add_displacement`
Hyps: (a) none -/
theorem sum_violWeight_le_live {t ε δ : ℚ} (hε : 0 < ε) (hδ : 0 < δ) (a c F : ℕ → ℝ)
    (d : ℕ → ℕ) (K : ℕ) :
    ∑ k ∈ range K, violWeight t ε δ (a (d k)) (c (d k)) ≤
      ∑ k ∈ range K, frozenWeight t ε δ (a (d k)) (F (d k)) *
          (if c (d k) < (t : ℝ) - ε then (1 : ℝ) else 0) +
        (2 / (ε : ℝ)) * ∑ k ∈ range K, |c (d k) - F (d k)| := by
  rw [mul_sum, ← sum_add_distrib]
  exact sum_le_sum fun k _ => violWeight_le_frozen_mul_live_add_displacement hε hδ _ _ _

end Cleanroom.Fa.FaDelayBsi
