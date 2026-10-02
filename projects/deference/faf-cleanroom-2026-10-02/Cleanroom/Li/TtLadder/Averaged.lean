import Cleanroom.Li.TtLadder.Arrows

/-!
# `tt-ladder`: averaged Total Trust from summable violation weight

Target 4 of [[tt-ladder-mandate]]: the notes' Corollary ("the Theorem ⇒ the averaged form"),
proved once over an abstract `[0,1]`-valued gate `g` and a credence `e ≥ 0`, then instantiated
to the ladder's `TSeq ⇒ AvgSeq`, along a schedule, and composed with `L_cond`. The deep-day
identity "`w_n = g_n` where `e_n ≤ t − ε − δ`" is *derived* from the ramp's saturation
(`ctsInd_eq_one_iff`), never assumed (trust-lab-061 (d)). Over real sequences; not a theorem
about inductors.
-/

namespace Cleanroom.Li.TtLadder

open LogicalInduction Filter Topology
open Cleanroom.Found.LiAsympCalc

/-- A weighted average of nonnegative values under nonnegative weights is nonnegative (both
branches of FAF's total `weightedAverage`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem weightedAverage_nonneg {g e : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) (he : ∀ n, 0 ≤ e n) (N : ℕ) :
    0 ≤ weightedAverage g e N := by
  unfold weightedAverage
  split_ifs with h
  · exact le_rfl
  · exact div_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hg i) (he i)))
      (prefixSum_nonneg hg N)

/-- **The averaged lemma** (the notes' Corollary, over an abstract gate). For a `[0,1]`-valued
gate `g` with divergent mass, a credence `e ≥ 0`, and a summable margin-`ε` violation weight
`g_n · Ind_δ(e_n < t − ε)`: the gate-weighted average of `e` is `≳ₙ t − ε − δ`. Proof: on
deep days (`e_n ≤ t − ε − δ`) the ramp saturates, so the weight *is* `g_n`; on the other days
`e_n > t − ε − δ`; hence `θ (g_n − w_n) ≤ g_n e_n` termwise with `θ := t − ε − δ`, and the
deep mass `∑ w` is bounded over a divergent denominator. The bound is vacuous for
`t ≤ ε + δ` (the average is `≥ 0`, `weightedAverage_nonneg`). No upper bound on `e` is used.
Witnesses of the *full* hypothesis package: `averaged_package_solid_creep` (`G ≡ 1`, creeping
`e`, four deep days; `WitnessesConst.lean`) and `averaged_package_harmonic_creep` (the
harmonic gate `1/(n+1)`, divergent, against the same `e`; `Witnesses.lean`). Gap and alt are
strictness witnesses of the instance `T ⇒ Avg` (`Avg ∧ ¬T`), not package witnesses: their
weights are not summable. The lower bound `0 ≤ e` is load-bearing: `avgSeq_needs_lower_bound`
(`Bounds.lean`) has a `[0,1]` quote, a summable weight and divergent gate mass against a
credence unbounded below, and its gated average is `≤ 0`. Over real sequences; not a theorem
about inductors.
Source: root-fa-006 (v3 Cor 4; [[faithful-acceleration]] l.159–167); lean-deference-045; trust-lab-061 (d); root-fa-2-005 Cor 1
Kind: P
Fidelity: variant: sequence-level; exact relative to the source's sequence claim (`e ≤ 1` not needed)
Hyps: (a) none -/
theorem averaged_of_summable {g e : ℕ → ℝ} {t ε δ : ℚ} (hδ : 0 < δ)
    (hg : ∀ n, g n ∈ Set.Icc (0 : ℝ) 1) (he : ∀ n, 0 ≤ e n)
    (hdiv : Tendsto (prefixSum g) atTop atTop)
    (hs : Summable (fun n => g n * ctsInd δ ((t : ℝ) - ε) (e n))) :
    AsympGE (weightedAverage g e) (fun _ => (t : ℝ) - ε - δ) := by
  set θ : ℝ := (t : ℝ) - ε - δ with hθ
  set w : ℕ → ℝ := fun n => g n * ctsInd δ ((t : ℝ) - ε) (e n) with hw
  have hw0 : ∀ n, 0 ≤ w n := fun n => mul_nonneg (hg n).1 (ctsInd_nonneg _ _ _)
  have hwg : ∀ n, w n ≤ g n := fun n =>
    mul_le_of_le_one_right (hg n).1 (ctsInd_le_one _ _ _)
  have hpt : ∀ n, θ * (g n - w n) ≤ g n * e n := by
    intro n
    rcases le_or_gt (e n) θ with hdeep | hnot
    · have hone : ctsInd δ ((t : ℝ) - ε) (e n) = 1 :=
        (ctsInd_eq_one_iff hδ _ _).2 (by rw [hθ] at hdeep; linarith)
      have hwn : w n = g n := by simp only [hw, hone, mul_one]
      rw [hwn, sub_self, mul_zero]
      exact mul_nonneg (hg n).1 (he n)
    · rcases le_or_gt 0 θ with hθ0 | hθ0
      · calc θ * (g n - w n) ≤ θ * g n :=
            mul_le_mul_of_nonneg_left (by linarith [hw0 n]) hθ0
          _ ≤ g n * e n := by nlinarith [(hg n).1]
      · calc θ * (g n - w n) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hθ0.le (by linarith [hwg n])
          _ ≤ g n * e n := mul_nonneg (hg n).1 (he n)
  have hsum : ∀ N, θ * prefixSum g N - θ * prefixSum w N ≤
      prefixSum (fun i => g i * e i) N := by
    intro N
    unfold prefixSum
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun i _ => by rw [← mul_sub]; exact hpt i)
  have hS : ∀ N, prefixSum w N ≤ ∑' n, w n :=
    fun N => hs.sum_le_tsum _ (fun i _ => hw0 i)
  have hratio : Tendsto (fun N => (∑' n, w n) / prefixSum g N) atTop (𝓝 0) :=
    hdiv.const_div_atTop _
  intro η hη
  have hev1 := eventually_prefixSum_pos hdiv
  have hev2 := hratio.eventually (gt_mem_nhds (show (0 : ℝ) < η / (|θ| + 1) by positivity))
  filter_upwards [hev1, hev2] with N hpos hsm
  show θ ≤ weightedAverage g e N + η
  rw [weightedAverage_eq_div hpos.ne']
  have hW0 : 0 ≤ prefixSum w N := prefixSum_nonneg hw0 N
  have hWS := hS N
  have hle : θ - θ * (prefixSum w N / prefixSum g N) ≤
      prefixSum (fun i => g i * e i) N / prefixSum g N := by
    rw [le_div_iff₀ hpos]
    have : (θ - θ * (prefixSum w N / prefixSum g N)) * prefixSum g N =
        θ * prefixSum g N - θ * prefixSum w N := by
      field_simp
    rw [this]
    exact hsum N
  have hr : |θ * (prefixSum w N / prefixSum g N)| < η := by
    rw [abs_mul]
    have h1 : |prefixSum w N / prefixSum g N| ≤ (∑' n, w n) / prefixSum g N := by
      rw [abs_of_nonneg (div_nonneg hW0 hpos.le)]
      exact div_le_div_of_nonneg_right hWS hpos.le
    have h2 : |θ| * (η / (|θ| + 1)) < η := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg θ]
    calc |θ| * |prefixSum w N / prefixSum g N|
        ≤ |θ| * ((∑' n, w n) / prefixSum g N) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ |θ| * (η / (|θ| + 1)) := mul_le_mul_of_nonneg_left hsm.le (abs_nonneg _)
      _ < η := h2
  linarith [hle, hr, le_abs_self (θ * (prefixSum w N / prefixSum g N))]

/-- **(iii) `T(t,ε,δ) ⇒ Avg(t,ε,δ)`** for `e ≥ 0`: the ladder's averaged arrow, an instance of
`averaged_of_summable` at the gate `gateSeq t δ a`. Strict: `avgSeq_not_tSeq_gap` and the
alternating witness (`Witnesses.lean`). Over real sequences; not a theorem about inductors.
Source: root-fa-006; lean-deference-2-002 (C11); [[faithful-acceleration]] l.130 (the fourth rung)
Kind: L
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem avgSeq_of_tSeq {a e : ℕ → ℝ} {t ε δ : ℚ} (hδ : 0 < δ) (he : ∀ n, 0 ≤ e n)
    (h : TSeq a e t ε δ) : AvgSeq a e t ε δ :=
  fun hdiv => averaged_of_summable hδ (gateSeq_mem_Icc t δ a) he hdiv h

/-- `T_∀ε(t,δ) ⇒ Avg(t,ε,δ)` for every `ε > 0` and `e ≥ 0`.
Source: lean-deference-2-002
Kind: L
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem avgSeq_of_tAllEpsSeq {a e : ℕ → ℝ} {t δ : ℚ} (hδ : 0 < δ) (he : ∀ n, 0 ≤ e n)
    (h : TAllEpsSeq a e t δ) {ε : ℚ} (hε : 0 < ε) : AvgSeq a e t ε δ :=
  avgSeq_of_tSeq hδ he (h ε hε)

/-- **(vii) `L_cond(t) ⇒ Avg(t,ε,δ)`** for every `ε > 0` and `e ≥ 0` (composition through
`T_∀ε`).
Source: lean-deference-2-002
Kind: L
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem avgSeq_of_lCondSeq {a e : ℕ → ℝ} {t δ : ℚ} (hδ : 0 < δ) (he : ∀ n, 0 ≤ e n)
    (h : LCondSeq a e t) {ε : ℚ} (hε : 0 < ε) : AvgSeq a e t ε δ :=
  avgSeq_of_tSeq hδ he (tSeq_of_lCondSeq hδ h hε)

/-- **Cor 1 along a schedule** (root-fa-2-005): `T(t,ε,δ)` of the reindexed pair
`(a ∘ d, e ∘ d)` gives `Avg(t,ε,δ)` of that pair — the averaged lemma at the gate `g ∘ d`.
Source: root-fa-2-005 (Cor 1 along `d`)
Kind: L
Fidelity: variant: sequence-level; stronger: `d` need not be strictly increasing
Hyps: (a) none -/
theorem avgSeq_comp_of_tSeq_comp {a e : ℕ → ℝ} {t ε δ : ℚ} (hδ : 0 < δ) (he : ∀ n, 0 ≤ e n)
    (d : ℕ → ℕ) (h : TSeq (a ∘ d) (e ∘ d) t ε δ) : AvgSeq (a ∘ d) (e ∘ d) t ε δ :=
  avgSeq_of_tSeq hδ (fun k => he (d k)) h

/-- The averaged bound is vacuous when `t ≤ ε + δ`: every `e ≥ 0` satisfies `Avg(t,ε,δ)` then,
whatever `a` (the average is nonnegative). Recorded so the bound's content is not oversold.
Source: [[faithful-acceleration]] l.167 ("for `t ≤ ε + δ` the bound is vacuous")
Kind: L
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem avgSeq_of_nonpos {a e : ℕ → ℝ} {t ε δ : ℚ} (ht : (t : ℝ) ≤ ε + δ) (he : ∀ n, 0 ≤ e n) :
    AvgSeq a e t ε δ := by
  intro _ η hη
  refine Eventually.of_forall (fun N => ?_)
  have := weightedAverage_nonneg (gateSeq_nonneg t δ a) he N
  show (t : ℝ) - ε - δ ≤ weightedAverage (gateSeq t δ a) e N + η
  linarith

end Cleanroom.Li.TtLadder
