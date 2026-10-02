import Cleanroom.Li.TtLadder.Witnesses

/-!
# `tt-ladder`: the middle-rung repair — support-nondegeneracy collapses the middle

Target 6 of [[tt-ladder-mandate]]. The notes' "limit ⇒ bounded-ε-violation" arrow is false
for soft gates (`middle_rung_false`, `Witnesses.lean`) because a shrinking gate damps the
product while the violation mass diverges. It is repaired exactly when the gate is
*effectively hard* — bounded away from `0` where positive (`SupportNondegenerate`): then
`L_prod ⇒ T_∀ε`, and in fact the three middle nodes `L_prod`, `L_cond`, `T_∀ε` coincide, with
**no** `[0,1]` bounds on `e` (Prop A's lower bound is not needed under the proviso, since the
proviso itself bounds the gate below on its support). This is the precise content of "the
arrow holds for hard gates" and of root-fa-007's flag about the `δ` convention: with a hard
indicator the top arrow's direction is as printed; with the soft ramp it is the proviso that
restores it. Over real sequences; not a theorem about inductors.
-/

namespace Cleanroom.Li.TtLadder

open LogicalInduction Filter Topology
open Cleanroom.Found.LiAsympCalc

/-! ## The repaired arrow -/

/-- **The repair**: under `SupportNondegenerate t δ a`, `L_prod(t,δ)` makes every violation
weight eventually `0`: on the weight's support `e n < t − ε` and `G_n ≥ c`, so
`G_n (e_n − t) < −εc`, contradicting `G (e − t) ≳ₙ 0`. Over real sequences; not a theorem
about inductors.
Source: trust-lab-061 (c); root-deference-2-006 (the bounded-gate lemma); lean-deference-046
Kind: P
Fidelity: variant: sequence-level; stronger: every weight is eventually `0`, no bounds on `e`
Hyps: (a) none -/
theorem eventually_viol_eq_zero_of_lProdSeq {a e : ℕ → ℝ} {t δ : ℚ} (hδ : 0 < δ)
    (hs : SupportNondegenerate t δ a) (h : LProdSeq a e t δ) {ε : ℚ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, viol e a t ε δ n = 0 := by
  obtain ⟨c, hc, hsupp⟩ := hs
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  filter_upwards [h (ε * c) (mul_pos hεR hc)] with n hn
  have hn' : (0 : ℝ) ≤ gateSeq t δ a n * (e n - t) + ε * c := hn
  by_contra hne
  have hpos : 0 < viol e a t ε δ n := lt_of_le_of_ne (viol_nonneg _ _ _ _ _ _) (Ne.symm hne)
  obtain ⟨h1, h2⟩ := dsWeight_pos_imp hδ hpos
  have hGpos : 0 < gateSeq t δ a n := (gateSeq_pos_iff hδ a n).2 h1
  have hcG := hsupp n hGpos
  have h3 : gateSeq t δ a n * (e n - t) < gateSeq t δ a n * (-ε) :=
    mul_lt_mul_of_pos_left (by linarith) hGpos
  have h4 : ε * c ≤ ε * gateSeq t δ a n := mul_le_mul_of_nonneg_left hcG hεR.le
  nlinarith

/-- **`middle_rung_repaired`**: under `SupportNondegenerate`, `L_prod(t,δ) ⇒ T_∀ε(t,δ)` — the
notes' arrow, valid exactly where the gate is effectively hard.
Source: trust-lab-061 (c) (`middle_rung_repaired`); root-deference-2-006; [[li-deference]] l.263–272 (the "holds with the margin" claim, true only under this proviso)
Kind: P
Fidelity: variant: sequence-level (the note's arrow plus the proviso)
Hyps: (a) none -/
theorem tAllEpsSeq_of_lProdSeq_of_supportNondegenerate {a e : ℕ → ℝ} {t δ : ℚ} (hδ : 0 < δ)
    (hs : SupportNondegenerate t δ a) (h : LProdSeq a e t δ) : TAllEpsSeq a e t δ := by
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_viol_eq_zero_of_lProdSeq hδ hs h hε)
  exact summable_of_ne_finset_zero (s := Finset.range N)
    (fun n hn => hN n (not_lt.1 (fun h' => hn (Finset.mem_range.2 h'))))

/-! ## The middle collapses -/

/-- Under `SupportNondegenerate`, `L_prod(t,δ) ⇒ L_cond(t)`: on gate days `G_n ≥ c`, so
`G_n (t − e_n) < cc'/2` eventually forces `t − e_n < c'`.
Source: [[tt-ladder-mandate]] target 6 (strengthening); trust-lab-061 (c)
Kind: P
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem lCondSeq_of_lProdSeq_of_supportNondegenerate {a e : ℕ → ℝ} {t δ : ℚ} (hδ : 0 < δ)
    (hs : SupportNondegenerate t δ a) (h : LProdSeq a e t δ) : LCondSeq a e t := by
  obtain ⟨c, hc, hsupp⟩ := hs
  intro c' hc'
  filter_upwards [h (c * c' / 2) (by positivity)] with n hn hg
  have hn' : (0 : ℝ) ≤ gateSeq t δ a n * (e n - t) + c * c' / 2 := hn
  have hGpos := (gateSeq_pos_iff hδ a n).2 hg
  have hcG := hsupp n hGpos
  by_contra hle
  push Not at hle
  have h1 : gateSeq t δ a n * (e n - t) ≤ gateSeq t δ a n * (-c') :=
    mul_le_mul_of_nonneg_left (by linarith) hGpos.le
  have h2 : c' * c ≤ c' * gateSeq t δ a n := mul_le_mul_of_nonneg_left hcG hc'.le
  nlinarith

/-- Under `SupportNondegenerate`, `T_∀ε(t,δ) ⇒ L_prod(t,δ)` with **no** lower bound on `e`
(compare Prop A, `lProdSeq_of_tAllEpsSeq`, which needs `0 ≤ e`): if `G_n (e_n − t) < −η`
frequently then `G_n > 0` there, so `G_n ≥ c`, and `e_n − t < −η` (as `G ≤ 1`); the weight at a
rational margin `ε ∈ (η/4, η/2)` is then `≥ c · min 1 (η/(2δ))` frequently.
Source: [[tt-ladder-mandate]] target 6 (strengthening)
Kind: P
Fidelity: variant: sequence-level; stronger: no bounds on `e`
Hyps: (a) none -/
theorem lProdSeq_of_tAllEpsSeq_of_supportNondegenerate {a e : ℕ → ℝ} {t δ : ℚ} (hδ : 0 < δ)
    (hs : SupportNondegenerate t δ a) (h : TAllEpsSeq a e t δ) : LProdSeq a e t δ := by
  obtain ⟨c, hc, hsupp⟩ := hs
  by_contra hcon
  unfold LProdSeq AsympGE AsympLE at hcon
  push Not at hcon
  obtain ⟨η, hη, hfreq⟩ := hcon
  obtain ⟨ε, hε1, hε2⟩ := exists_rat_btwn (show η / 4 < η / 2 by linarith)
  have hεpos : 0 < ε := by
    have : (0 : ℝ) < ε := by linarith
    exact_mod_cast this
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hmpos : 0 < c * min 1 ((η / 2) / δ) :=
    mul_pos hc (lt_min one_pos (div_pos (by linarith) hδR))
  have hfv : ∃ᶠ n in atTop, c * min 1 ((η / 2) / δ) ≤ viol e a t ε δ n := by
    refine hfreq.mono (fun n hn => ?_)
    have hG := gateSeq_mem_Icc t δ a n
    have hGpos : 0 < gateSeq t δ a n := by
      by_contra h0
      push Not at h0
      have h00 : gateSeq t δ a n = 0 := le_antisymm h0 hG.1
      rw [h00, zero_mul] at hn
      linarith
    have h1 : e n - t < -η := by
      by_contra hle
      push Not at hle
      have := mul_le_mul_of_nonneg_left hle hG.1
      nlinarith [hG.2]
    have hcG := hsupp n hGpos
    rw [viol_eq_gateSeq_mul]
    have h3 : min 1 ((η / 2) / δ) ≤ ctsInd δ ((t : ℝ) - ε) (e n) :=
      min_one_div_le_ctsInd hδ (by linarith)
    exact mul_le_mul hcG h3 (le_min zero_le_one (div_nonneg (by linarith) hδR.le)) hG.1
  have hev := summable_eventually_lt (h ε hεpos) hmpos
  obtain ⟨n, hn1, hn2⟩ := (hfv.and_eventually hev).exists
  linarith

/-- **The middle collapses under support-nondegeneracy**: for `δ > 0` and a gate bounded away
from `0` where positive, `L_prod(t,δ) ⟺ L_cond(t) ⟺ T_∀ε(t,δ)`, with no bounds on `e`. This
is what "the arrow holds for hard gates" means, exactly; the harmonic gate of W4
(`witness_gate_no_gap`) shows the proviso is not automatic.
Source: [[tt-ladder-mandate]] target 6; trust-lab-061 (c); root-deference-2-006; root-fa-007 (flag)
Kind: P
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem middle_rung_repaired_iff {a e : ℕ → ℝ} {t δ : ℚ} (hδ : 0 < δ)
    (hs : SupportNondegenerate t δ a) :
    (LProdSeq a e t δ ↔ LCondSeq a e t) ∧ (LCondSeq a e t ↔ TAllEpsSeq a e t δ) :=
  ⟨⟨lCondSeq_of_lProdSeq_of_supportNondegenerate hδ hs, lProdSeq_of_lCondSeq hδ⟩,
    ⟨tAllEpsSeq_of_lCondSeq hδ, fun h =>
      lCondSeq_of_lProdSeq_of_supportNondegenerate hδ hs
        (lProdSeq_of_tAllEpsSeq_of_supportNondegenerate hδ hs h)⟩⟩

/-! ## Non-vacuity of the proviso -/

/-- Any quote that never lands in the gate's ramp zone `(t, t + cδ)` (for some `0 < c ≤ 1`) has
a support-nondegenerate gate; in particular hard-ish gates (`a ≡ t + δ`, `c = 1`).
Source: trust-lab-061 (c) ("in particular hard gates"); root-deference-2-006 (`g_n ∈ {0} ∪ [γ,1]`)
Kind: L
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem supportNondegenerate_of_avoids_ramp {t δ : ℚ} (hδ : 0 < δ) {a : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (h : ∀ n, a n ≤ t ∨ (t : ℝ) + c * δ ≤ a n) :
    SupportNondegenerate t δ a := by
  refine ⟨c, hc, fun n hpos => ?_⟩
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  rcases h n with h1 | h1
  · exact absurd ((gateSeq_pos_iff hδ a n).1 hpos) (not_lt.2 h1)
  · have := min_one_div_le_ctsInd hδ (x := a n) (y := (t : ℝ)) (r := c * δ) (by linarith)
    rw [mul_div_assoc, div_self hδR.ne', mul_one, min_eq_right hc1] at this
    exact this

/-- The constant hard quote `a ≡ t + δ` has a support-nondegenerate gate.
Source: trust-lab-061 (c)
Kind: N−
Fidelity: n/a
Hyps: n/a -/
theorem supportNondegenerate_const {t δ : ℚ} (hδ : 0 < δ) :
    SupportNondegenerate t δ (fun _ => (t : ℝ) + δ) :=
  supportNondegenerate_of_avoids_ramp hδ one_pos le_rfl (fun _ => Or.inr (by linarith))

/-- **`witness_gate_no_gap`** (the trust lab's name): W4's harmonic gate `1/(n+1)` visibly
violates support-nondegeneracy — it is positive on every day and below every `c > 0` on some
day.
Source: trust-lab-061 (c) (`witness_gate_no_gap`); trust-lab-060
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem witness_gate_no_gap : ¬ SupportNondegenerate (1/2) (1/10) (harmQuote (1/2) (1/10)) := by
  rintro ⟨c, hc, hsupp⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hc
  have h1 := hsupp n (by rw [gateSeq_harmQuote (by norm_num)]; positivity)
  rw [gateSeq_harmQuote (by norm_num)] at h1
  linarith

/-- The two-valued quote alternating `3/5` (gate `1`) and `1/2` (gate `0`) at `t = 1/2`,
`δ = 1/10`.
Source: [[tt-ladder-mandate]] target 6 (non-vacuity: `a` alternating `t` and `t + δ`)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def altQuote' (n : ℕ) : ℝ := if Even n then 3/5 else 1/2

/-- **N+ witness of the repaired arrow's full hypothesis package**: the non-constant two-valued
gate of `altQuote'` (in `{0, 1}`) is support-nondegenerate, and the creeping credence
`1/2 − 1/(n+2)` satisfies `L_prod` against it; the repaired arrow then yields `T_∀ε`. Both
sequences non-constant, both `[0,1]`-valued.
Source: [[tt-ladder-mandate]] target 6 (non-vacuity)
Kind: N+
Fidelity: n/a
Hyps: n/a -/
theorem repair_witness :
    (∀ n, altQuote' n ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ n, creepE n ∈ Set.Icc (0 : ℝ) 1) ∧
    SupportNondegenerate (1/2) (1/10) altQuote' ∧
    LProdSeq altQuote' creepE (1/2) (1/10) ∧
    TAllEpsSeq altQuote' creepE (1/2) (1/10) := by
  have hbounds : ∀ n, altQuote' n ∈ Set.Icc (0 : ℝ) 1 := fun n => by
    unfold altQuote'; split_ifs <;> norm_num
  have hs : SupportNondegenerate (1/2) (1/10) altQuote' :=
    supportNondegenerate_of_avoids_ramp (by norm_num) one_pos le_rfl (fun n => by
      unfold altQuote'
      split_ifs
      · right; norm_num
      · left; norm_num)
  have hl : LProdSeq altQuote' creepE (1/2) (1/10) := by
    intro η hη
    filter_upwards [tendsto_one_div_add_two.eventually (gt_mem_nhds hη)] with n hn
    show (0 : ℝ) ≤ gateSeq (1/2) (1/10) altQuote' n * (creepE n - ((1/2 : ℚ) : ℝ)) + η
    have hG := gateSeq_mem_Icc (1/2) (1/10) altQuote' n
    have hce : creepE n - ((1/2 : ℚ) : ℝ) = -(1 / ((n : ℝ) + 2)) := by
      unfold creepE; push_cast; ring
    rw [hce]
    nlinarith [hG.1, hG.2]
  exact ⟨hbounds, fun n => ⟨(creepE_bounds n).1, by linarith [(creepE_bounds n).2]⟩, hs, hl,
    tAllEpsSeq_of_lProdSeq_of_supportNondegenerate (by norm_num) hs hl⟩

end Cleanroom.Li.TtLadder
