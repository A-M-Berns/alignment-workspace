import Cleanroom.Fa.FaDelayBsi.Split

/-!
# `fa-delay-bsi` · Pipeline (T9): the cross-generational "conservation law", sequence-level

The sources' "conservation law" (BSI §6 line 108, FA-critique msg 43, lean-deference-058:
"each freeze adds its own surprise flow to an un-certifiable residue that nothing later redeems")
is prose — "still not a theorem", flagged ill-posed. The nearest well-posed version, at the level
of real sequences: a chain `e 0, e 1, …, e K` of day-`n` values (`e 0 = c` the human's live
credence, `e (j+1)` generation `j+1`'s quote of generation `j`'s value), link thresholds
`t_j := t − (K−1−j)·ε'`, link margin `ε' − 2δ`. **Ramp pigeonhole**: if the end-to-end weight
`Ind_δ(e K > t + δ) · Ind_δ(e 0 < t − K·ε' − δ)` is positive then some link `j < K` has
`e (j+1) ≥ t_j + δ` and `e j < t_j − ε' + δ`, and that link's violation weight is exactly `1`.
Hence the end-to-end weight is at most the sum of the link weights (`pipeline_bound`), and
composing T2 per link gives the iterated deficit inequality (`pipeline_deficit`): end-to-end
misplaced trust is at most the sum over generations of (that generation's frozen part) plus
`2/(ε'−2δ)` times that generation's within-freeze displacement. Kind `L`, `variant:
sequence-level`. The inductor-level law (each link an inductor pair with its own freeze) is not
stated: it has no named package here (findings).
-/

namespace Cleanroom.Fa.FaDelayBsi

open LogicalInduction Cleanroom.Found.LiAsympCalc
open Finset

/-- **Link thresholds** of a `K`-link pipeline: `t_j := t − (K − 1 − j)·ε'` for `j < K`, so
`t_{K−1} = t` and consecutive thresholds differ by `ε'`.
Source: [[fa-delay-bsi-mandate]] T9 (the mandate's sketch, constants fixed here)
Kind: D
Fidelity: variant: sequence-level
Hyps: n/a -/
def linkThreshold (t ε' : ℚ) (K j : ℕ) : ℚ := t - ((K : ℚ) - 1 - j) * ε'

/-- **Link `j`'s violation weight**: `violWeight` at threshold `t_j`, margin `ε' − 2δ`, width `δ`,
quote `e (j+1)` (the next generation's value) against credence `e j`.
Source: [[fa-delay-bsi-mandate]] T9; BSI §6 line 108 (lean-deference-058)
Kind: D
Fidelity: variant: sequence-level
Hyps: n/a -/
noncomputable def linkWeight (δ t ε' : ℚ) (K : ℕ) (e : ℕ → ℝ) (j : ℕ) : ℝ :=
  violWeight (linkThreshold t ε' K j) (ε' - 2 * δ) δ (e (j + 1)) (e j)

/-- **The end-to-end weight**: `Ind_δ(e K > t + δ) · Ind_δ(e 0 < t − K·ε' − δ)` — the last
generation advertises above `t + δ` while the human's live credence sits below `t − K·ε' − δ`.
Source: [[fa-delay-bsi-mandate]] T9
Kind: D
Fidelity: variant: sequence-level
Hyps: n/a -/
noncomputable def endToEndWeight (δ t ε' : ℚ) (K : ℕ) (e : ℕ → ℝ) : ℝ :=
  ctsInd δ (e K) ((t : ℝ) + δ) * ctsInd δ ((t : ℝ) - K * ε' - δ) (e 0)

/-- The cast of a link threshold.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem linkThreshold_cast (t ε' : ℚ) (K j : ℕ) :
    ((linkThreshold t ε' K j : ℚ) : ℝ) = (t : ℝ) - ((K : ℝ) - 1 - j) * ε' := by
  unfold linkThreshold; push_cast; ring

/-- **T9 (headline). The ramp pigeonhole.** If `e K ≥ t + δ` and `e 0 < t − K·ε' + δ` then some
link `j < K` has `e (j+1) ≥ t_j + δ` and `e j < t_j − ε' + δ`. Downward induction from the top:
if no link is bad, `e (K − i) ≥ t − i·ε' + δ` for every `i ≤ K`, contradicting the bottom bound at
`i = K`.
Scope: sequence-level.
Source: [[fa-delay-bsi-mandate]] T9 ("a ramp pigeonhole"); BSI §6 line 108 (lean-deference-058)
Kind: L
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem pipeline_pigeonhole {δ : ℚ} (t ε' : ℚ) (K : ℕ) (e : ℕ → ℝ)
    (htop : (t : ℝ) + δ ≤ e K) (hbot : e 0 < (t : ℝ) - K * ε' + δ) :
    ∃ j < K, ((linkThreshold t ε' K j : ℚ) : ℝ) + δ ≤ e (j + 1) ∧
      e j < ((linkThreshold t ε' K j : ℚ) : ℝ) - ε' + δ := by
  by_contra hno
  push Not at hno
  have key : ∀ i ≤ K, (t : ℝ) - i * ε' + δ ≤ e (K - i) := by
    intro i
    induction i with
    | zero => intro _; simpa using htop
    | succ i ih =>
      intro hi
      have hiK : i < K := by omega
      have h1 := ih hiK.le
      have hj : K - i = (K - (i + 1)) + 1 := by omega
      rw [hj] at h1
      have hthr : ((linkThreshold t ε' K (K - (i + 1)) : ℚ) : ℝ) = (t : ℝ) - i * ε' := by
        rw [linkThreshold_cast]
        have : ((K - (i + 1) : ℕ) : ℝ) = (K : ℝ) - (i + 1) := by
          rw [Nat.cast_sub hi]; push_cast; ring
        rw [this]; ring
      have h2 := hno (K - (i + 1)) (by omega) (by rw [hthr]; linarith)
      rw [hthr] at h2
      push_cast
      linarith
  have := key K le_rfl
  rw [Nat.sub_self] at this
  linarith

/-- At a bad link the link weight is exactly `1` (both ramps saturate).
Source: [[fa-delay-bsi-mandate]] T9
Kind: L
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem linkWeight_eq_one {δ : ℚ} (hδ : 0 < δ) (t ε' : ℚ) (K : ℕ) (e : ℕ → ℝ) (j : ℕ)
    (h1 : ((linkThreshold t ε' K j : ℚ) : ℝ) + δ ≤ e (j + 1))
    (h2 : e j < ((linkThreshold t ε' K j : ℚ) : ℝ) - ε' + δ) :
    linkWeight δ t ε' K e j = 1 := by
  unfold linkWeight
  refine (violWeight_eq_one_iff hδ _ _ _ _).2 ⟨h1, ?_⟩
  push_cast
  linarith

/-- **T9 (headline). The end-to-end weight is at most the sum of the link weights**:
`endToEndWeight ≤ ∑_{j<K} linkWeight j`. If the end-to-end weight is positive, the pigeonhole
gives a link of weight `1`, and the end-to-end weight is at most `1`.
Scope: sequence-level.
Source: [[fa-delay-bsi-mandate]] T9; BSI §6 line 108 (lean-deference-058: "each freeze adds its own surprise flow")
Kind: L
Fidelity: variant: sequence-level (the sources' law is prose)
Hyps: (a) none -/
theorem pipeline_bound {δ : ℚ} (hδ : 0 < δ) (t ε' : ℚ) (K : ℕ) (e : ℕ → ℝ) :
    endToEndWeight δ t ε' K e ≤ ∑ j ∈ range K, linkWeight δ t ε' K e j := by
  have hnonneg : ∀ j ∈ range K, 0 ≤ linkWeight δ t ε' K e j := fun j _ =>
    violWeight_nonneg _ _ _ _ _
  rcases (le_or_gt (endToEndWeight δ t ε' K e) 0) with h0 | hpos
  · exact h0.trans (sum_nonneg hnonneg)
  · unfold endToEndWeight at hpos
    have hq : 0 < ctsInd δ (e K) ((t : ℝ) + δ) := by
      rcases (ctsInd_nonneg δ (e K) ((t : ℝ) + δ)).lt_or_eq with h | h
      · exact h
      · rw [← h, zero_mul] at hpos; exact absurd hpos (lt_irrefl 0)
    have hc : 0 < ctsInd δ ((t : ℝ) - K * ε' - δ) (e 0) := by
      rcases (ctsInd_nonneg δ ((t : ℝ) - K * ε' - δ) (e 0)).lt_or_eq with h | h
      · exact h
      · rw [← h, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
    have htop : (t : ℝ) + δ ≤ e K := ((ctsInd_pos_iff hδ _ _).1 hq).le
    have hbot : e 0 < (t : ℝ) - K * ε' + δ := by
      have := (ctsInd_pos_iff hδ _ _).1 hc
      have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
      linarith
    obtain ⟨j, hjK, hj1, hj2⟩ := pipeline_pigeonhole t ε' K e htop hbot
    have hone := linkWeight_eq_one hδ t ε' K e j hj1 hj2
    have hle1 : endToEndWeight δ t ε' K e ≤ 1 :=
      mul_le_one₀ (ctsInd_le_one _ _ _) (ctsInd_nonneg _ _ _) (ctsInd_le_one _ _ _)
    calc endToEndWeight δ t ε' K e ≤ 1 := hle1
      _ = linkWeight δ t ε' K e j := hone.symm
      _ ≤ ∑ j ∈ range K, linkWeight δ t ε' K e j :=
          single_le_sum hnonneg (mem_range.2 hjK)

/-- **T9, the iterated deficit inequality** (T2 composed per link). With frozen values `F j` for
each generation and link margin `ε'' := ε' − 2δ > 0`:
`endToEndWeight ≤ ∑_{j<K} frozenWeight t_j ε'' δ (e (j+1)) (F j) + (2/ε'') ∑_{j<K} |e j − F j|` —
the end-to-end misplaced trust is bounded by the generations' frozen parts plus their
within-freeze displacements. This is what the "conservation law" metaphor supports at the level
of sequences.
Scope: sequence-level.
Source: BSI §6 line 108 (lean-deference-058); FA-critique msg 43 line 3042; [[fa-delay-bsi-mandate]] T9
Kind: L
Fidelity: variant: sequence-level (the sources' law is prose, flagged ill-posed)
Hyps: (a) none -/
theorem pipeline_deficit {δ t ε' : ℚ} (hδ : 0 < δ) (hε : 0 < ε' - 2 * δ) (K : ℕ)
    (e F : ℕ → ℝ) :
    endToEndWeight δ t ε' K e ≤
      ∑ j ∈ range K, frozenWeight (linkThreshold t ε' K j) (ε' - 2 * δ) δ (e (j + 1)) (F j) +
        (2 / ((ε' - 2 * δ : ℚ) : ℝ)) * ∑ j ∈ range K, |e j - F j| := by
  refine (pipeline_bound hδ t ε' K e).trans ?_
  rw [mul_sum, ← sum_add_distrib]
  exact sum_le_sum fun j _ => violWeight_le_frozen_add_displacement hε hδ _ _ _

end Cleanroom.Fa.FaDelayBsi
