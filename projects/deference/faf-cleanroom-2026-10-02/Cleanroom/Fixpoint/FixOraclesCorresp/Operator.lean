import Cleanroom.Fixpoint.FixOraclesCorresp.Lifts
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Data.Real.Sign
import Mathlib.Analysis.Normed.Group.Basic

/-!
# `Cleanroom.Fixpoint.FixOraclesCorresp.Operator`: the fixed-point operator is not continuous

Target 6 (fixpoint-lit-006/007). The notes claim "the fixed point operator `FP : CGC → P(Δ(X))` is
continuous with respect to the Hausdorff metric" (theoretical-insights §6; `ReflectiveOracles.lean:54`)
without a topology on `CGC`. Under the natural reading — the family varies continuously in sup norm,
fixed-point sets are compared in Hausdorff distance — it is false: `shrinkTo c ε p = (1−ε) p + ε c` is
affine for every `ε`, `ε ↦ shrinkTo c ε` is sup-norm continuous, its fixed-point set in `Δ(X)` is `{c}`
for `ε > 0` and all of `Δ(X)` at `ε = 0`, and the Hausdorff distance between the two stays `≥ 1/2` for
`|X| ≥ 2` (`hausdorffDist_fixSet_shrinkTo_ge`, `not_tendsto_hausdorffDist_fixSet`). By target 3 the same
statement holds for the Dirac and collapse fixed points of the barycentric lifts.

Also here, 007: the notes' motivating example `g_ε x = x + ε·sign x` on `[−1, 1]` is neither continuous
at `0` nor a self-map of `[−1, 1]` (for `ε > 0`); the corrected `h_ε x = max (−1) (min 1 (x + ε))` is a
continuous self-map with `Fix h₀ = [−1, 1]`, `Fix h_ε = {1}` (`ε > 0`), `{−1}` (`ε < 0`); and
`Fix (x ↦ x³) = {−1, 0, 1}` is not convex — the precise content of "the fixed-point operator is not
Kakutani".
-/

namespace Cleanroom.Fixpoint.FixOraclesCorresp

open Set Filter Topology

variable {X : Type*} [Fintype X]

/-- The affine family `shrinkTo c ε p = (1 − ε) • p + ε • c`.
Source: [[fixpoint-lit-inventory]] 006 (`f_ε(p) = (1−ε)p + εc`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def shrinkTo (c : X → ℝ) (ε : ℝ) (p : X → ℝ) : X → ℝ := (1 - ε) • p + ε • c

/-- The fixed-point set of `f` in `Δ(X)`.
Source: [[fixpoint-lit-inventory]] 006 (`Fix(f_ε)`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def fixSet (f : (X → ℝ) → (X → ℝ)) : Set (X → ℝ) := {p | p ∈ stdSimplex ℝ X ∧ f p = p}

omit [Fintype X] in
/-- `shrinkTo c ε` is affine (on every set).
Source: [[fixpoint-lit-inventory]] 006 ("is affine")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem affineOn_shrinkTo (c : X → ℝ) (ε : ℝ) (K : Set (X → ℝ)) : AffineOn (shrinkTo c ε) K := by
  intro p _ q _ t _
  ext x
  simp only [shrinkTo, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- `shrinkTo c ε` maps `Δ(X)` to itself for `c ∈ Δ(X)`, `ε ∈ [0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem shrinkTo_mapsTo {c : X → ℝ} (hc : c ∈ stdSimplex ℝ X) {ε : ℝ} (hε : ε ∈ Icc (0 : ℝ) 1) :
    MapsTo (shrinkTo c ε) (stdSimplex ℝ X) (stdSimplex ℝ X) := fun p hp =>
  convex_stdSimplex ℝ X hp hc (by linarith [hε.2]) hε.1 (by ring)

/-- `Fix (shrinkTo c ε) ∩ Δ(X) = {c}` for `ε > 0`.
Source: [[fixpoint-lit-inventory]] 006 ("`Fix(f_ε) = {c}` for `ε > 0`")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem fixSet_shrinkTo_pos {c : X → ℝ} (hc : c ∈ stdSimplex ℝ X) {ε : ℝ} (hε : 0 < ε) :
    fixSet (shrinkTo c ε) = {c} := by
  ext p
  simp only [fixSet, mem_setOf_eq, mem_singleton_iff]
  constructor
  · rintro ⟨-, h⟩
    ext x
    have hx := congrFun h x
    simp only [shrinkTo, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx
    have : ε * (c x - p x) = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hε.ne'
    · linarith
  · rintro rfl
    refine ⟨hc, ?_⟩
    ext x
    simp only [shrinkTo, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- `Fix (shrinkTo c 0) ∩ Δ(X) = Δ(X)`.
Source: [[fixpoint-lit-inventory]] 006 ("`Fix(f₀) = Δ(X)`")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem fixSet_shrinkTo_zero (c : X → ℝ) : fixSet (shrinkTo c 0) = stdSimplex ℝ X := by
  ext p
  simp only [fixSet, mem_setOf_eq]
  constructor
  · exact fun h => h.1
  · intro hp
    refine ⟨hp, ?_⟩
    ext x
    simp [shrinkTo]

/-- **Sup-norm continuity of the family**: `‖shrinkTo c ε p − p‖ ≤ ε` on `Δ(X)` (coordinates of
simplex points differ by at most `1`).
Source: [[fixpoint-lit-inventory]] 006 ("`G_{f_ε} → G_{f_0}` … as `ε → 0`")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem norm_shrinkTo_sub_le {c : X → ℝ} (hc : c ∈ stdSimplex ℝ X) {p : X → ℝ}
    (hp : p ∈ stdSimplex ℝ X) {ε : ℝ} (hε : 0 ≤ ε) : ‖shrinkTo c ε p - p‖ ≤ ε := by
  have : shrinkTo c ε p - p = ε • (c - p) := by
    ext x; simp only [shrinkTo, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [this, norm_smul, Real.norm_of_nonneg hε]
  refine le_trans (mul_le_mul_of_nonneg_left ?_ hε) (le_of_eq (mul_one ε))
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro x
  have h1 : c x ≤ 1 := by simpa using (stdSimplex_subset_Icc ℝ hc).2 x
  have h2 : p x ≤ 1 := by simpa using (stdSimplex_subset_Icc ℝ hp).2 x
  have h3 := hc.1 x
  have h4 := hp.1 x
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- **Target 6 (006), the headline: `Fix` is not Hausdorff-continuous along an affine, sup-norm
continuous family.** For `|X| ≥ 2`, `c ∈ Δ(X)` and every `ε > 0`,
`hausdorffDist (Fix (shrinkTo c ε)) (Fix (shrinkTo c 0)) ≥ 1/2`: the second set is all of `Δ(X)`, the
first is `{c}`, and some vertex `e_i` has `c i ≤ 1/2`, so `dist e_i c ≥ 1/2`.
Source: [[fixpoint-lit-inventory]] 006 (theoretical-insights §6 "Continuity"; mathematical-formulation
§6 (2)–(3); `ReflectiveOracles.lean:54`) — refuted under the natural reading
Kind: P
Fidelity: variant: the note gives no topology on `CGC`; this is the sup-norm/Hausdorff reading
Hyps: (a) none — this is a refutation -/
theorem hausdorffDist_fixSet_shrinkTo_ge (hX : 2 ≤ Fintype.card X) {c : X → ℝ}
    (hc : c ∈ stdSimplex ℝ X) {ε : ℝ} (hε : 0 < ε) :
    1 / 2 ≤ Metric.hausdorffDist (fixSet (shrinkTo c ε)) (fixSet (shrinkTo c 0)) := by
  classical
  haveI : Nonempty X := Fintype.card_pos_iff.1 (by omega)
  rw [fixSet_shrinkTo_pos hc hε, fixSet_shrinkTo_zero, Metric.hausdorffDist_comm]
  -- a vertex with `c i ≤ 1/2`
  obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le (Finset.univ_nonempty (α := X))
    (show ∑ x, c x ≤ ∑ _x : X, (1 / 2 : ℝ) by
      rw [hc.2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have : (2 : ℝ) ≤ Fintype.card X := by exact_mod_cast hX
      linarith)
  have hfin : Metric.hausdorffEDist (stdSimplex ℝ X) ({c} : Set (X → ℝ)) ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded ⟨_, single_mem_stdSimplex ℝ i⟩
      ⟨c, rfl⟩ (isCompact_stdSimplex ℝ X).isBounded Bornology.isBounded_singleton
  have h1 := Metric.infDist_le_hausdorffDist_of_mem (single_mem_stdSimplex ℝ i) hfin
  rw [Metric.infDist_singleton] at h1
  refine le_trans ?_ h1
  refine le_trans ?_ (dist_le_pi_dist (Pi.single i (1 : ℝ)) c i)
  rw [Pi.single_eq_same, Real.dist_eq, abs_sub_comm]
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- **Target 6 (006), as a non-convergence statement**: the Hausdorff distance between
`Fix (shrinkTo c ε)` and `Fix (shrinkTo c 0)` does not tend to `0` as `ε → 0⁺`, although
`shrinkTo c ε → shrinkTo c 0` uniformly on `Δ(X)` (`norm_shrinkTo_sub_le`).
Source: [[fixpoint-lit-inventory]] 006
Kind: P
Fidelity: variant: sup-norm/Hausdorff reading
Hyps: (a) none — this is a refutation -/
theorem not_tendsto_hausdorffDist_fixSet (hX : 2 ≤ Fintype.card X) {c : X → ℝ}
    (hc : c ∈ stdSimplex ℝ X) :
    ¬ Tendsto (fun ε => Metric.hausdorffDist (fixSet (shrinkTo c ε)) (fixSet (shrinkTo c 0)))
      (𝓝[>] 0) (𝓝 0) := by
  intro h
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Metric.hausdorffDist (fixSet (shrinkTo c ε)) (fixSet (shrinkTo c 0)) < 1 / 2 :=
    (tendsto_order.1 h).2 _ (by norm_num)
  obtain ⟨ε, hlt, hε⟩ := (hev.and self_mem_nhdsWithin).exists
  exact absurd (hausdorffDist_fixSet_shrinkTo_ge hX hc hε) (not_le.2 hlt)

/-! ### The bridge to the notes' objects: the same jump inside `CGC` -/

/-- `baryLift (shrinkTo c ε)` is a member of the notes' class `CGC` (nonempty convex values in `Δ²`
and a convex graph) for `c ∈ Δ(X)`, `ε ∈ [0, 1]`: `shrinkTo c ε` is affine and maps `Δ(X)` to itself.
Source: [[fixpoint-lit-inventory]] 006 ("`G_{f_ε}` … in `CGC`")
Kind: L
Fidelity: variant: Δ² finitely supported
Hyps: none -/
theorem hasConvexGraph_baryLift_shrinkTo {c : X → ℝ} (hc : c ∈ stdSimplex ℝ X) {ε : ℝ}
    (hε : ε ∈ Icc (0 : ℝ) 1) : HasConvexGraph (baryLift (shrinkTo c ε)) :=
  (hasConvexGraph_baryLift_iff (shrinkTo_mapsTo hc hε)).2 (affineOn_shrinkTo c ε _)

/-- The Dirac fixed points of `baryLift (shrinkTo c ε)` are `fixSet (shrinkTo c ε)` (target 3 (iii)).
Source: [[fixpoint-lit-inventory]] 006 with 003 (iii)
Kind: L
Fidelity: variant: Δ² finitely supported
Hyps: none -/
theorem diracFixedPoints_baryLift_shrinkTo (c : X → ℝ) (ε : ℝ) :
    {p | IsDiracFixedPoint (baryLift (shrinkTo c ε)) p} = fixSet (shrinkTo c ε) := by
  ext p
  simp only [mem_setOf_eq, isDiracFixedPoint_baryLift_iff, fixSet]

/-- The collapse fixed points of `baryLift (shrinkTo c ε)` are `fixSet (shrinkTo c ε)` (target 3 (iv)).
Source: [[fixpoint-lit-inventory]] 006 with 003 (iv)
Kind: L
Fidelity: variant: Δ² finitely supported
Hyps: none -/
theorem collapseFixedPoints_baryLift_shrinkTo {c : X → ℝ} (hc : c ∈ stdSimplex ℝ X) {ε : ℝ}
    (hε : ε ∈ Icc (0 : ℝ) 1) :
    {p | IsCollapseFixedPoint (baryLift (shrinkTo c ε)) p} = fixSet (shrinkTo c ε) := by
  ext p
  simp only [mem_setOf_eq, isCollapseFixedPoint_baryLift_iff (shrinkTo_mapsTo hc hε), fixSet]

/-- **Target 6 (006) on the notes' own objects**: along the family `baryLift (shrinkTo c ε)` of
convex-graph correspondences (both endpoints are members of `CGC`), the Dirac fixed-point set jumps:
Hausdorff distance `≥ 1/2` between the fixed-point set at `ε ∈ (0, 1]` and the one at `ε = 0`, for
`|X| ≥ 2`. This is the form that refutes the notes' sentence "`FP : CGC → P(Δ(X))` is continuous"
with `FP` acting on correspondences, as the notes write it.
Source: [[fixpoint-lit-inventory]] 006 (theoretical-insights §6 "Continuity";
`ReflectiveOracles.lean:54`) — refuted under the natural reading
Kind: P
Fidelity: variant: Δ² finitely supported; the sup-norm/Hausdorff reading (the note gives no topology)
Hyps: (a) none — this is a refutation; (c) carrier: Δ² as finitely supported measures -/
theorem hausdorffDist_diracFixedPoints_baryLift_shrinkTo_ge (hX : 2 ≤ Fintype.card X) {c : X → ℝ}
    (hc : c ∈ stdSimplex ℝ X) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) 1) :
    HasConvexGraph (baryLift (shrinkTo c ε)) ∧ HasConvexGraph (baryLift (shrinkTo c 0)) ∧
      1 / 2 ≤ Metric.hausdorffDist {p | IsDiracFixedPoint (baryLift (shrinkTo c ε)) p}
        {p | IsDiracFixedPoint (baryLift (shrinkTo c 0)) p} := by
  refine ⟨hasConvexGraph_baryLift_shrinkTo hc ⟨hε.1.le, hε.2⟩,
    hasConvexGraph_baryLift_shrinkTo hc ⟨le_rfl, zero_le_one⟩, ?_⟩
  rw [diracFixedPoints_baryLift_shrinkTo, diracFixedPoints_baryLift_shrinkTo]
  exact hausdorffDist_fixSet_shrinkTo_ge hX hc hε.1

/-- **Target 6 (006) on the notes' objects, as non-convergence**: the Hausdorff distance between the
Dirac fixed-point sets of `baryLift (shrinkTo c ε)` and of `baryLift (shrinkTo c 0)` does not tend to
`0` as `ε → 0⁺`.
Source: [[fixpoint-lit-inventory]] 006
Kind: P
Fidelity: variant: Δ² finitely supported; sup-norm/Hausdorff reading
Hyps: (a) none — this is a refutation; (c) carrier: Δ² as finitely supported measures -/
theorem not_tendsto_hausdorffDist_diracFixedPoints_baryLift (hX : 2 ≤ Fintype.card X) {c : X → ℝ}
    (hc : c ∈ stdSimplex ℝ X) :
    ¬ Tendsto (fun ε => Metric.hausdorffDist {p | IsDiracFixedPoint (baryLift (shrinkTo c ε)) p}
      {p | IsDiracFixedPoint (baryLift (shrinkTo c 0)) p}) (𝓝[>] 0) (𝓝 0) := by
  simp_rw [diracFixedPoints_baryLift_shrinkTo]
  exact not_tendsto_hausdorffDist_fixSet hX hc

/-! ### 007: the motivating example over `ℝ`, corrected -/

/-- The notes' `g_ε x = x + ε · sign x`.
Source: [[fixpoint-lit-inventory]] 007 (mathematical-formulation §2)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def gSign (ε x : ℝ) : ℝ := x + ε * Real.sign x

/-- `g_ε` is not continuous at `0` for `ε ≠ 0` (it jumps by `ε`).
Source: [[fixpoint-lit-inventory]] 007 ("discontinuous at `0`") — a local error in the note
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem gSign_not_continuousAt {ε : ℝ} (hε : ε ≠ 0) : ¬ ContinuousAt (gSign ε) 0 := by
  intro h
  have h0 : gSign ε 0 = 0 := by simp [gSign]
  have := Metric.tendsto_nhds.1 h (|ε| / 2) (by positivity)
  rw [Metric.eventually_nhds_iff] at this
  obtain ⟨η, hη, hball⟩ := this
  set x := min (η / 2) (|ε| / 4) with hx
  have hxpos : 0 < x := lt_min (by positivity) (by positivity)
  have hx1 : x ≤ η / 2 := min_le_left _ _
  have hx2 : x ≤ |ε| / 4 := min_le_right _ _
  have hd := hball (show dist x 0 < η by rw [Real.dist_eq, sub_zero, abs_of_pos hxpos]; linarith)
  rw [h0, Real.dist_eq, sub_zero] at hd
  have hg : gSign ε x = x + ε := by simp [gSign, Real.sign_of_pos hxpos]
  rw [hg] at hd
  have key : |ε| ≤ |x + ε| + |x| := by
    have := abs_sub_abs_le_abs_sub ε (x + ε)
    rw [show ε - (x + ε) = -x by ring, abs_neg] at this
    linarith
  rw [abs_of_pos hxpos] at key
  have := abs_pos.2 hε
  linarith

/-- `g_ε` is not a self-map of `[−1, 1]` for `ε > 0` (`g_ε 1 = 1 + ε`).
Source: [[fixpoint-lit-inventory]] 007 ("not a self-map of `[−1, 1]`") — a local error in the note
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem gSign_not_mapsTo {ε : ℝ} (hε : 0 < ε) : ¬ MapsTo (gSign ε) (Icc (-1) 1) (Icc (-1) 1) := by
  intro h
  have := (h (show (1 : ℝ) ∈ Icc (-1) 1 from ⟨by norm_num, le_rfl⟩)).2
  simp [gSign, Real.sign_of_pos (zero_lt_one' ℝ)] at this
  linarith

/-- The corrected example `h_ε x = max (−1) (min 1 (x + ε))`: shift and clamp.
Source: [[fixpoint-lit-inventory]] 007 (corrected claim)
Kind: D
Fidelity: variant: corrected example
Hyps: n/a -/
noncomputable def hClamp (ε x : ℝ) : ℝ := max (-1) (min 1 (x + ε))

/-- `h_ε` is continuous.
Source: [[fixpoint-lit-inventory]] 007
Kind: L
Fidelity: n/a
Hyps: none -/
theorem continuous_hClamp (ε : ℝ) : Continuous (hClamp ε) := by
  unfold hClamp; fun_prop

/-- `h_ε` maps everything into `[−1, 1]`.
Source: [[fixpoint-lit-inventory]] 007
Kind: L
Fidelity: n/a
Hyps: none -/
theorem hClamp_mem_Icc (ε x : ℝ) : hClamp ε x ∈ Icc (-1 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- `Fix h₀ = [−1, 1]`.
Source: [[fixpoint-lit-inventory]] 007
Kind: P
Fidelity: variant: corrected example
Hyps: (a) none -/
theorem fixedPoints_hClamp_zero : {x | hClamp 0 x = x} = Icc (-1 : ℝ) 1 := by
  ext x
  simp only [mem_setOf_eq]
  constructor
  · intro h; rw [← h]; exact hClamp_mem_Icc 0 x
  · rintro ⟨h1, h2⟩
    simp only [hClamp, add_zero]
    rw [min_eq_right h2, max_eq_right h1]

/-- `Fix h_ε = {1}` for `ε > 0`.
Source: [[fixpoint-lit-inventory]] 007
Kind: P
Fidelity: variant: corrected example
Hyps: (a) none -/
theorem fixedPoints_hClamp_pos {ε : ℝ} (hε : 0 < ε) : {x | hClamp ε x = x} = {1} := by
  ext x
  simp only [mem_setOf_eq, mem_singleton_iff, hClamp]
  constructor
  · intro h
    rcases le_or_gt 1 (x + ε) with h1 | h1
    · rw [min_eq_left h1, max_eq_right (by norm_num)] at h
      exact h.symm
    · rw [min_eq_right h1.le] at h
      rcases le_or_gt (-1) (x + ε) with h2 | h2
      · rw [max_eq_right h2] at h; linarith
      · rw [max_eq_left h2.le] at h; linarith
  · rintro rfl
    rw [min_eq_left (by linarith), max_eq_right (by norm_num)]

/-- `Fix h_ε = {−1}` for `ε < 0`.
Source: [[fixpoint-lit-inventory]] 007
Kind: P
Fidelity: variant: corrected example
Hyps: (a) none -/
theorem fixedPoints_hClamp_neg {ε : ℝ} (hε : ε < 0) : {x | hClamp ε x = x} = {-1} := by
  ext x
  simp only [mem_setOf_eq, mem_singleton_iff, hClamp]
  constructor
  · intro h
    rcases le_or_gt (x + ε) (-1) with h1 | h1
    · rw [min_eq_right (by linarith), max_eq_left h1] at h
      exact h.symm
    · rcases le_or_gt (x + ε) 1 with h2 | h2
      · rw [min_eq_right h2, max_eq_right h1.le] at h; linarith
      · rw [min_eq_left h2.le, max_eq_right (by norm_num)] at h; linarith
  · rintro rfl
    rw [min_eq_right (by linarith), max_eq_left (by linarith)]

/-- `Fix (x ↦ x³) = {−1, 0, 1}`.
Source: [[fixpoint-lit-inventory]] 007 ("`Fix(f)` need not be convex (`f(x) = x³`)")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem fixedPoints_cube : {x : ℝ | x ^ 3 = x} = {-1, 0, 1} := by
  ext x
  simp only [mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · intro h
    have : x * ((x - 1) * (x + 1)) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · exact Or.inr (Or.inl h0)
    · rcases mul_eq_zero.1 h0 with h1 | h1
      · exact Or.inr (Or.inr (by linarith))
      · exact Or.inl (by linarith)
  · rintro (rfl | rfl | rfl) <;> norm_num

/-- **The fixed-point set of a continuous self-map need not be convex** — the precise content of "the
fixed-point operator is not Kakutani": `Fix (x ↦ x³)` contains `0` and `1` but not `1/2`.
Source: [[fixpoint-lit-inventory]] 007
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem not_convex_fixedPoints_cube : ¬ Convex ℝ {x : ℝ | x ^ 3 = x} := by
  intro h
  have h0 : (0 : ℝ) ∈ {x : ℝ | x ^ 3 = x} := by simp
  have h1 : (1 : ℝ) ∈ {x : ℝ | x ^ 3 = x} := by simp
  have := h h0 h1 (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, mem_setOf_eq] at this
  norm_num at this

end Cleanroom.Fixpoint.FixOraclesCorresp
