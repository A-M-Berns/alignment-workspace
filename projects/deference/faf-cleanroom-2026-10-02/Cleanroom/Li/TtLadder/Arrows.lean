import Cleanroom.Li.TtLadder.Defs
import Mathlib.Order.Filter.Cofinite

/-!
# `tt-ladder`: the Hasse diagram at fixed `t, δ` — the arrows

Target 2 of [[tt-ladder-mandate]]: the sound arrows between the readings of `Defs.lean`, at a
fixed rational threshold `t` and width `δ > 0`, over real sequences `a` (a quote) and `e` (a
credence). The non-arrows are witnessed in `Witnesses.lean`; the averaged arrow
`TSeq → AvgSeq` is `Averaged.lean`'s.

Corrected fixed-`t` order (the notes' printed ladder is inverted, see [[tt-ladder-findings]]):
`BV ⇒ T_∀ε ⇒ T(t,ε) ⇒ Avg`, with `L_cond ⇒ T_∀ε`, `L_cond ⇒ L_prod`, and Prop A
`T_∀ε ⇒ L_prod` (which needs `e` bounded below — `e ≥ 0` here; without a lower bound it is
false, `prop_a_needs_lower_bound` in `Witnesses.lean`).

Ramp facts proved here that `li-asymp-calc` lacks: monotonicity of `ctsInd` in its first
argument, antitonicity in its second, and the lower bound `min 1 (r/δ) ≤ ctsInd δ x y` when
`r ≤ x - y`.

Also here (target 1's `L` rows for `L_cond`): `L_cond(t)` is true on a finitely-touched gate
whatever the credence (`lCondSeq_of_finite_gate`), is the `∀ c > 0, ∀ᶠ` statement along the
restricted filter `atTop ⊓ 𝓟 {n ∣ t < a n}` (`lCondSeq_iff_eventually_inf_principal`), and for
an infinitely-touched gate and `e ∈ [0,1]` is `t ≤ liminf e` along that filter
(`lCondSeq_iff_liminf`) — the sources' "`liminf_{n : a_n > t} e_n ≥ t`" literally.
-/

namespace Cleanroom.Li.TtLadder

open LogicalInduction Filter Topology
open Cleanroom.Found.LiAsympCalc

/-! ## Ramp monotonicity -/

/-- The ramp is monotone in its first argument (positive width).
Source: none: infrastructure ([[tt-ladder-mandate]] target 1)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem ctsInd_mono_left {δ : ℚ} (hδ : 0 < δ) {x x' : ℝ} (h : x ≤ x') (y : ℝ) :
    ctsInd δ x y ≤ ctsInd δ x' y := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold ctsInd
  refine min_le_min_left 1 (max_le_max_left 0 ?_)
  exact div_le_div_of_nonneg_right (by linarith) hδR.le

/-- The ramp is antitone in its second argument (positive width).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem ctsInd_anti_right {δ : ℚ} (hδ : 0 < δ) (x : ℝ) {y y' : ℝ} (h : y ≤ y') :
    ctsInd δ x y' ≤ ctsInd δ x y := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold ctsInd
  refine min_le_min_left 1 (max_le_max_left 0 ?_)
  exact div_le_div_of_nonneg_right (by linarith) hδR.le

/-- Lower bound on the ramp from a lower bound on the gap: `r ≤ x - y` gives
`min 1 (r / δ) ≤ ctsInd δ x y`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem min_one_div_le_ctsInd {δ : ℚ} (hδ : 0 < δ) {x y r : ℝ} (h : r ≤ x - y) :
    min 1 (r / δ) ≤ ctsInd δ x y := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold ctsInd
  refine min_le_min_left 1 ?_
  calc r / δ ≤ (x - y) / δ := div_le_div_of_nonneg_right h hδR.le
    _ ≤ max 0 ((x - y) / δ) := le_max_right _ _

/-- The violation weight is antitone in the margin: a smaller margin `ε' ≤ ε` gives a larger
weight, termwise (the ramp `ctsInd δ (t - ε) e` is monotone in `t - ε`).
Source: [[tt-ladder-mandate]] target 1 ("`viol` is monotone in `ε`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem viol_anti_eps {δ : ℚ} (hδ : 0 < δ) (a e : ℕ → ℝ) (t : ℚ) {ε ε' : ℚ} (h : ε' ≤ ε)
    (n : ℕ) : viol e a t ε δ n ≤ viol e a t ε' δ n := by
  rw [viol_eq_gateSeq_mul, viol_eq_gateSeq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (gateSeq_nonneg _ _ _ _)
  refine ctsInd_mono_left hδ ?_ _
  have : (ε' : ℝ) ≤ ε := by exact_mod_cast h
  linarith

/-! ## The monotone arrows -/

/-- **(i) `BV(t,δ) ⇒ T_∀ε(t,δ)`**: bounded margin-free violation gives bounded ε-violation for
every rational margin — termwise `viol e a t ε δ n ≤ viol e a t 0 δ n`. Over real sequences; not
a theorem about inductors.
Source: lean-deference-2-002 (C7); root-fa-007; [[li-deference]] l.243 (first link, corrected form)
Kind: L
Fidelity: variant: sequence-level; exact relative to the source's sequence claim
Hyps: (a) none -/
theorem tAllEpsSeq_of_bvSeq {a e : ℕ → ℝ} {t δ : ℚ} (hδ : 0 < δ) (h : BVSeq a e t δ) :
    TAllEpsSeq a e t δ := by
  intro ε hε
  rw [bvSeq_iff_summable_viol_zero] at h
  exact h.of_nonneg_of_le (fun n => viol_nonneg a e t ε δ n)
    (fun n => viol_anti_eps hδ a e t hε.le n)

/-- **(ii) `T_∀ε(t,δ) ⇒ T(t,ε,δ)`**: the single instance.
Source: lean-deference-2-002
Kind: L
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem tSeq_of_tAllEpsSeq {a e : ℕ → ℝ} {t δ : ℚ} (h : TAllEpsSeq a e t δ) {ε : ℚ}
    (hε : 0 < ε) : TSeq a e t ε δ :=
  h ε hε

/-- **(v) `L_cond(t) ⇒ T_∀ε(t,δ)`**: if the credence is eventually never undercut by any margin
on gate-touched days, every violation weight is eventually `0` (on gate days the violation ramp
vanishes, off gate days the gate does), hence summable. Over real sequences; not a theorem
about inductors.
Source: lean-deference-2-002 ("finitely many gate-touched days with `E^H < t − ε`")
Kind: L
Fidelity: variant: sequence-level; stronger: every weight is eventually `0`, not merely summable
Hyps: (a) none -/
theorem eventually_viol_eq_zero_of_lCondSeq {a e : ℕ → ℝ} {t δ : ℚ} (hδ : 0 < δ)
    (h : LCondSeq a e t) {ε : ℚ} (hε : 0 < ε) : ∀ᶠ n in atTop, viol e a t ε δ n = 0 := by
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  filter_upwards [h ε hεR] with n hn
  rw [viol_eq_gateSeq_mul]
  by_cases hg : (t : ℝ) < a n
  · have := hn hg
    rw [(ctsInd_eq_zero_iff hδ _ _).2 (by linarith), mul_zero]
  · rw [(gateSeq_eq_zero_iff hδ a n).2 (not_lt.1 hg), zero_mul]

/-- **(v) `L_cond(t) ⇒ T_∀ε(t,δ)`** (summability packaging of the previous lemma).
Source: lean-deference-2-002
Kind: L
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem tAllEpsSeq_of_lCondSeq {a e : ℕ → ℝ} {t δ : ℚ} (hδ : 0 < δ) (h : LCondSeq a e t) :
    TAllEpsSeq a e t δ := by
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_viol_eq_zero_of_lCondSeq hδ h hε)
  exact summable_of_ne_finset_zero (s := Finset.range N)
    (fun n hn => hN n (not_lt.1 (fun h' => hn (Finset.mem_range.2 h'))))

/-- **(vi) `L_cond(t) ⇒ L_prod(t,δ)`**: on gate days `e n - t > -c` and `G ≤ 1`, off gate days
`G = 0`. Over real sequences; not a theorem about inductors.
Source: lean-deference-2-002
Kind: L
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem lProdSeq_of_lCondSeq {a e : ℕ → ℝ} {t δ : ℚ} (hδ : 0 < δ) (h : LCondSeq a e t) :
    LProdSeq a e t δ := by
  intro η hη
  filter_upwards [h η hη] with n hn
  show (0 : ℝ) ≤ gateSeq t δ a n * (e n - t) + η
  have hG := gateSeq_mem_Icc t δ a n
  by_cases hg : (t : ℝ) < a n
  · have h1 := hn hg
    nlinarith [mul_nonneg hG.1 (show (0 : ℝ) ≤ e n - t + η by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 1 - gateSeq t δ a n by linarith [hG.2]) hη.le]
  · rw [(gateSeq_eq_zero_iff hδ a n).2 (not_lt.1 hg)]
    linarith

/-! ## Prop A -/

/-- **(iv) Prop A: `T_∀ε(t,δ) ⇒ L_prod(t,δ)`**, for a credence bounded below (`0 ≤ e`). If
`liminf G_n (e_n − t) < 0`, i.e. frequently `G_n (t − e_n) > η`, then on those days `t − e_n > η`
(as `G ≤ 1`) and `G_n > η / t` (as `t − e_n ≤ t`); at a rational margin `ε ∈ (η/4, η/2)` the
violation ramp is `≥ min 1 (η/(2δ))`, so the weight is frequently bounded below by a positive
constant and cannot tend to `0` — contradicting summability. The lower bound on `e` is
necessary (`prop_a_needs_lower_bound`, `Witnesses.lean`; the same pair has `BV`,
`bvSeq_needs_lower_bound`, `Bounds.lean`): with `e` unbounded below the product can diverge
while every weight is summable. Inhabitants of the full package (`0 ≤ e`, `T_∀ε`, and the
conclusion reached non-trivially): W2 (`sqQuote`, `e ≡ 0`, `T_∀ε` from `BV`) and creep
(`a ≡ 3/5`, `creepE`, `T_∀ε` from `L_cond`). Over real sequences; not a theorem about
inductors.
Source: lean-deference-2-002 (`T_∀ε ⟹ L_prod`, "the two-line proof"); lean-deference-046 (Prop A — whose summary states a gated-liminf conclusion at fixed `t` that carries the fixed-`t` artifact, F5)
Kind: P
Fidelity: variant: sequence-level; exact relative to the source's sequence claim under its standing `[0,1]` bounds (only `0 ≤ e` is used)
Hyps: (a) none -/
theorem lProdSeq_of_tAllEpsSeq {a e : ℕ → ℝ} {t δ : ℚ} (hδ : 0 < δ) (he : ∀ n, 0 ≤ e n)
    (h : TAllEpsSeq a e t δ) : LProdSeq a e t δ := by
  by_contra hcon
  unfold LProdSeq AsympGE AsympLE at hcon
  push Not at hcon
  obtain ⟨η, hη, hfreq⟩ := hcon
  have hfreq' : ∃ᶠ n in atTop, η < gateSeq t δ a n * ((t : ℝ) - e n) :=
    hfreq.mono (fun n hn => by
      have : gateSeq t δ a n * ((t : ℝ) - e n) = -(gateSeq t δ a n * (e n - t)) := by ring
      linarith)
  have ht : (0 : ℝ) < t := by
    obtain ⟨n, hn⟩ := hfreq'.exists
    by_contra htle
    push Not at htle
    have : gateSeq t δ a n * ((t : ℝ) - e n) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (gateSeq_nonneg _ _ _ _) (by linarith [he n])
    linarith
  obtain ⟨ε, hε1, hε2⟩ := exists_rat_btwn (show η / 4 < η / 2 by linarith)
  have hεpos : 0 < ε := by
    have : (0 : ℝ) < ε := by linarith
    exact_mod_cast this
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hmpos : 0 < (η / t) * min 1 ((η / 2) / δ) :=
    mul_pos (div_pos hη ht) (lt_min one_pos (div_pos (by linarith) hδR))
  have hfv : ∃ᶠ n in atTop, (η / t) * min 1 ((η / 2) / δ) ≤ viol e a t ε δ n := by
    refine hfreq'.mono (fun n hn => ?_)
    rw [viol_eq_gateSeq_mul]
    have hG := gateSeq_mem_Icc t δ a n
    have h1 : η < (t : ℝ) - e n := by
      by_contra hle
      push Not at hle
      nlinarith [mul_nonneg hG.1 hη.le, mul_nonneg (show (0 : ℝ) ≤ 1 - gateSeq t δ a n by
        linarith [hG.2]) (show (0 : ℝ) ≤ η by linarith), hG.1, hG.2]
    have h2 : η / t < gateSeq t δ a n := by
      rw [div_lt_iff₀ ht]
      have : gateSeq t δ a n * ((t : ℝ) - e n) ≤ gateSeq t δ a n * t :=
        mul_le_mul_of_nonneg_left (by linarith [he n]) hG.1
      linarith
    have h3 : min 1 ((η / 2) / δ) ≤ ctsInd δ ((t : ℝ) - ε) (e n) :=
      min_one_div_le_ctsInd hδ (by linarith)
    exact mul_le_mul h2.le h3
      (le_min zero_le_one (div_nonneg (by linarith) hδR.le)) hG.1
  have hlim := (h ε hεpos).tendsto_atTop_zero
  have hev : ∀ᶠ n in atTop, viol e a t ε δ n < (η / t) * min 1 ((η / 2) / δ) :=
    hlim.eventually (gt_mem_nhds hmpos)
  obtain ⟨n, hn1, hn2⟩ := (hfv.and_eventually hev).exists
  linarith

/-! ## Compositions -/

/-- **(vii) `BV(t,δ) ⇒ L_prod(t,δ)`** for `0 ≤ e`: the first link of `li-deference`'s chain and
the top arrow of the note's ladder under the *product* reading — sound (trust-lab-059's
`top_rung_sound`, re-proved over FAF's `ctsInd` as `BV ⇒ T_∀ε ⇒ L_prod`). Under the
*conditional* reading the top arrow is false (`tAllEpsSeq_bvSeq_not_lCondSeq`, `Witnesses.lean`).
Kind `L`, not `C`: it is the one-line composition (i)∘(iv); the content is Prop A's. Over real
sequences; not a theorem about inductors.
Source: trust-lab-059 (`top_rung_sound`); [[li-deference]] l.237–241; root-fa-007 (top arrow, product reading)
Kind: L
Fidelity: variant: sequence-level; exact (trust-lab-059's `0 ≤ p` hypothesis; its `t ≤ 1` is not needed)
Hyps: (a) none -/
theorem lProdSeq_of_bvSeq {a e : ℕ → ℝ} {t δ : ℚ} (hδ : 0 < δ) (he : ∀ n, 0 ≤ e n)
    (h : BVSeq a e t δ) : LProdSeq a e t δ :=
  lProdSeq_of_tAllEpsSeq hδ he (tAllEpsSeq_of_bvSeq hδ h)

/-- `L_cond(t) ⇒ T(t,ε,δ)` for every rational `ε > 0` (composition of (v) and (ii)).
Source: lean-deference-2-002
Kind: L
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem tSeq_of_lCondSeq {a e : ℕ → ℝ} {t δ : ℚ} (hδ : 0 < δ) (h : LCondSeq a e t) {ε : ℚ}
    (hε : 0 < ε) : TSeq a e t ε δ :=
  tAllEpsSeq_of_lCondSeq hδ h ε hε

/-! ## The `L_prod` bridge to the chat's `G_n (t − e_n)⁺ → 0` form -/

/-- `L_prod(t,δ)` is `G_n · max 0 (t − e_n) → 0` (the FA chat's spelling): `G ≥ 0` turns
`G (e − t) ≳ₙ 0` into the vanishing of the nonnegative shortfall product.
Source: lean-deference-2-001 (`L_prod(t)`: `G_n · (t − E^H_n)^+ → 0`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem lProdSeq_iff_tendsto (a e : ℕ → ℝ) (t δ : ℚ) :
    LProdSeq a e t δ ↔
      Tendsto (fun n => gateSeq t δ a n * max 0 ((t : ℝ) - e n)) atTop (𝓝 0) := by
  have hnn : ∀ n, 0 ≤ gateSeq t δ a n * max 0 ((t : ℝ) - e n) :=
    fun n => mul_nonneg (gateSeq_nonneg _ _ _ _) (le_max_left _ _)
  constructor
  · intro h
    rw [tendsto_order]
    refine ⟨fun b hb => Eventually.of_forall (fun n => lt_of_lt_of_le hb (hnn n)), ?_⟩
    intro η hη
    filter_upwards [h (η / 2) (by linarith)] with n hn
    have hn' : (0 : ℝ) ≤ gateSeq t δ a n * (e n - t) + η / 2 := hn
    have hG := gateSeq_mem_Icc t δ a n
    rcases le_or_gt ((t : ℝ) - e n) 0 with hle | hlt
    · rw [max_eq_left hle, mul_zero]; exact hη
    · rw [max_eq_right hlt.le]
      nlinarith
  · intro h η hη
    have := h.eventually (gt_mem_nhds hη)
    filter_upwards [this] with n hn
    show (0 : ℝ) ≤ gateSeq t δ a n * (e n - t) + η
    have hG := gateSeq_mem_Icc t δ a n
    rcases le_or_gt ((t : ℝ) - e n) 0 with hle | hlt
    · nlinarith [mul_nonneg hG.1 (show (0 : ℝ) ≤ e n - t by linarith)]
    · rw [max_eq_right hlt.le] at hn
      nlinarith

/-! ## `L_cond`: the finite-gate convention and the restricted-filter bridges -/

/-- `L_cond(t)` holds whenever the gate set `{n ∣ t < a n}` is finite, whatever the credence is
on those days — the sources' convention ("true when the gate is touched only finitely often"),
made kernel-visible. Over real sequences; not a theorem about inductors.
Source: [[tt-ladder-mandate]] target 1 (`LCondSeq`: "true when `{n ∣ t < a n}` is finite")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem lCondSeq_of_finite_gate {a : ℕ → ℝ} (e : ℕ → ℝ) {t : ℚ}
    (hS : {n | (t : ℝ) < a n}.Finite) : LCondSeq a e t := by
  intro c _
  obtain ⟨N, hN⟩ := hS.bddAbove
  filter_upwards [eventually_gt_atTop N] with n hn hlt
  exact absurd (hN hlt) (not_le.2 hn)

/-- `L_cond(t)` in restricted-filter form: `∀ c > 0, ∀ᶠ n in atTop ⊓ 𝓟 {n ∣ t < a n}, t − c < e n`
(`Filter.eventually_inf_principal`). Over real sequences; not a theorem about inductors.
Source: [[tt-ladder-mandate]] target 1 (the restricted-filter reading of `L_cond`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem lCondSeq_iff_eventually_inf_principal (a e : ℕ → ℝ) (t : ℚ) :
    LCondSeq a e t ↔
      ∀ c : ℝ, 0 < c → ∀ᶠ n in atTop ⊓ 𝓟 {n | (t : ℝ) < a n}, (t : ℝ) - c < e n := by
  unfold LCondSeq
  simp only [eventually_inf_principal, Set.mem_setOf_eq]

/-- **The `liminf` bridge for `L_cond`**: when the gate set `S = {n ∣ t < a n}` is infinite and
`e ∈ [0,1]`, `L_cond(t)` is `t ≤ liminf e (atTop ⊓ 𝓟 S)` — the sources'
"`liminf_{n : a_n > t} e_n ≥ t`" with the `liminf` taken along the gate-touched days. The
infinite gate set makes the restricted filter `NeBot` and the `[0,1]` bounds make the `liminf` a
genuine real (not a junk `sSup`); on a finite gate set the filter is `⊥` and `L_cond(t)` holds
outright (`lCondSeq_of_finite_gate`). Over real sequences; not a theorem about inductors.
Source: [[tt-ladder-mandate]] target 1 ("prove the equivalence with the restricted-filter `liminf` when `S` is infinite"); lean-deference-2-001 (`L_cond`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem lCondSeq_iff_liminf {a e : ℕ → ℝ} (he : ∀ n, e n ∈ Set.Icc (0 : ℝ) 1) {t : ℚ}
    (hS : {n | (t : ℝ) < a n}.Infinite) :
    LCondSeq a e t ↔ (t : ℝ) ≤ liminf e (atTop ⊓ 𝓟 {n | (t : ℝ) < a n}) := by
  haveI : NeBot (atTop ⊓ 𝓟 {n | (t : ℝ) < a n}) :=
    frequently_iff_neBot.1 (Nat.frequently_atTop_iff_infinite.2 hS)
  have hbdd : IsBoundedUnder (· ≥ ·) (atTop ⊓ 𝓟 {n | (t : ℝ) < a n}) e :=
    isBoundedUnder_of ⟨0, fun n => (he n).1⟩
  have hcobdd : IsCoboundedUnder (· ≥ ·) (atTop ⊓ 𝓟 {n | (t : ℝ) < a n}) e :=
    (isBoundedUnder_of ⟨1, fun n => (he n).2⟩ :
      IsBoundedUnder (· ≤ ·) (atTop ⊓ 𝓟 {n | (t : ℝ) < a n}) e).isCoboundedUnder_ge
  rw [le_liminf_iff hcobdd hbdd, lCondSeq_iff_eventually_inf_principal]
  constructor
  · intro h y hy
    have := h ((t : ℝ) - y) (by linarith)
    simpa only [sub_sub_cancel] using this
  · intro h c hc
    exact h ((t : ℝ) - c) (by linarith)

end Cleanroom.Li.TtLadder
