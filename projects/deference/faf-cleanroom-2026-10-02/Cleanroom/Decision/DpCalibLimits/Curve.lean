import Cleanroom.Decision.DpCalibLimits.Defs
import Cleanroom.Decision.DpCalibration.Miniature

/-!
# T7(e) — the miniature's curve (CA-10′), stretch

On Remark 4.3's miniature (`d` sampled upstream by an independent draw from `C(d)`, then queried
live; worlds `(sample, live)`) the run law of every procedure is the product `ν_C{(s, l)} =
C(d)(s) · C(d)(l)` (`miniature_nu_point`): live and sample are independent with *equal* marginals
(`miniature_nu_sample`, `miniature_nu_live`). So the calibration manifold `M_d` (Q2; `manifold` of
[[dp-calib-limits-mandate]] §3.7, over LF-admissible self-models) is exactly the curve
`{(m², m(1−m), m(1−m), (1−m)²) : m ∈ (0,1)}` (`miniature_manifold_iff`), and

* CA-10′'s off-curve state is confirmed: the product state with marginals `(½, ⅓)` lies on no
  point of the manifold — every manifold point has equal marginals
  (`manifold_equal_marginals`, `prodState_half_third_not_mem_manifold`);
* the convex hull of the manifold (Q2: "the credal candidate of Appendix B is its convex hull")
  strictly exceeds it: the midpoint of the curve points at `m = ¼` and `m = ¾` is a convex
  combination of two manifold points and is on no point of the curve
  (`miniature_hull_exceeds_manifold`).

The mandate's T7(e) pairs the product-state witness with the hull claim. It cannot witness it:
every point of the hull has equal marginals too (the marginals are linear), so the product state
with marginals `(½, ⅓)` is outside the hull as well (`prodState_half_third_not_in_hull`). CA-10′
itself says only "off the curve", which is true. Findings F19.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-! ## The run law on the miniature is a product -/

/-- Sample events by the world's first coordinate: `{(a, ·)}`, `{(b, ·)}`.
Source: CA-10′ ("live and sample independent with equal marginals"). Kind: D -/
def miniSampleEv (x : Act2) : Finset MiniW := Finset.univ.filter fun w => w.1 = x

/-- **The miniature's run law is the product of the label with itself**:
`ν_C(X) = ∑_{(s,l) ∈ X} C(d)(s) · C(d)(l)` for every procedure and event.
Source: CA-10′ ("Independent redraws: `M_d = {(c², c(1−c), c(1−c), (1−c)²)}`")
Kind: P
Fidelity: exact
Hyps: none -/
theorem miniature_nu_eq (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset MiniW) :
    nu C miniature X = ∑ w ∈ X, (C ()).w w.1 * (C ()).w w.2 := by
  have hX : (∑ w ∈ X, (C ()).w w.1 * (C ()).w w.2) =
      ∑ w : MiniW, if w ∈ X then (C ()).w w.1 * (C ()).w w.2 else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext w; simp
  rw [hX, Fintype.sum_prod_type, nu_eq_sum, miniature_sum]
  simp [miniature, leafLaw_decision, world_decision]

/-- `ν_C{(s, l)} = C(d)(s) · C(d)(l)`: CA-10′'s curve, coordinate by coordinate.
Source: CA-10′. Kind: L -/
theorem miniature_nu_point (C : Proc Unit (fun _ => Act2) ℚ) (s l : Act2) :
    nu C miniature {(s, l)} = (C ()).w s * (C ()).w l := by
  rw [miniature_nu_eq, Finset.sum_singleton]

/-- `ν_C(sample = a) = C(d)(a)`: the sample marginal equals the live marginal
(`miniature_nu_live`). Source: CA-10′ ("equal marginals"). Kind: L -/
theorem miniature_nu_sample (C : Proc Unit (fun _ => Act2) ℚ) (x : Act2) :
    nu C miniature (miniSampleEv x) = (C ()).w x := by
  rw [miniature_nu_eq, miniSampleEv, Finset.sum_filter, Fintype.sum_prod_type]
  have := (C ()).sum_one
  rw [Act2.sum_univ] at this
  cases x
  · simp [Act2.sum_univ]
    linear_combination (C ()).w Act2.a * this
  · simp [Act2.sum_univ]
    linear_combination (C ()).w Act2.b * this

/-! ## The manifold is the curve -/

/-- The curve point of a self-model `m`: `X ↦ ∑_{(s,l) ∈ X} m(s) m(l)`.
Source: CA-10′. Kind: D -/
def curvePt (m : FinDistr ℚ Act2) : Finset MiniW → ℚ := fun X => ∑ w ∈ X, m.w w.1 * m.w w.2

/-- **The calibration manifold at the miniature is the open curve**: a worldview `f` is on
`M_d` (for any procedure `C` — the LF-admissible self-models of a one-point tree do not depend on
`C`) iff `f = curvePt m` for a full-support `m`. (`O_d = ⊤`, `ν(⊤) = 1`, so the manifold's
cross-multiplied clause is `f X = ν_{C[d ↦ m]}(X)`, and `miniature_nu_eq` gives the product.)
Source: Q2 ([[decision-problems-v2]] line 297); CA-10′ ("`M_d = {(c², c(1−c), c(1−c), (1−c)²)}` …
a curve (rank 1) in the 3-simplex"); mandate T7(e)
Kind: P
Fidelity: exact (the open curve: the manifold's self-models are full-support, so the endpoints
`m ∈ {0, 1}` are excluded)
Hyps: none -/
theorem miniature_manifold_iff (C : Proc Unit (fun _ => Act2) ℚ) (f : Finset MiniW → ℚ) :
    f ∈ manifold miniObs C miniature () ↔
      ∃ m : FinDistr ℚ Act2, (∀ x, 0 < m.w x) ∧ f = curvePt m := by
  constructor
  · rintro ⟨C', ⟨m, hm, rfl⟩, _, hf⟩
    refine ⟨m, hm, funext fun X => ?_⟩
    have h := hf X
    simp only [miniObs, Finset.inter_univ, nu_univ, mul_one] at h
    rw [h, miniature_nu_eq, curvePt]
    simp [Proc.deviate_same]
  · rintro ⟨m, hm, rfl⟩
    refine ⟨C.deviate () m, ⟨m, hm, rfl⟩, ?_, fun X => ?_⟩
    · simp only [miniObs]; exact nu_univ_pos _ _
    · simp only [miniObs, Finset.inter_univ, nu_univ, mul_one]
      rw [miniature_nu_eq, curvePt]
      simp [Proc.deviate_same]

/-- Every full-support curve point is on the manifold. Source: CA-10′. Kind: L -/
theorem curvePt_mem_manifold (C : Proc Unit (fun _ => Act2) ℚ) (m : FinDistr ℚ Act2)
    (hm : ∀ x, 0 < m.w x) : curvePt m ∈ manifold miniObs C miniature () :=
  (miniature_manifold_iff C _).2 ⟨m, hm, rfl⟩

/-- **Every manifold point has equal marginals**: `f(sample = a) = f(live = a)`.
Source: CA-10′ ("live and sample independent with *equal* marginals"). Kind: C -/
theorem manifold_equal_marginals (C : Proc Unit (fun _ => Act2) ℚ) (f : Finset MiniW → ℚ)
    (hf : f ∈ manifold miniObs C miniature ()) :
    f (miniSampleEv .a) = f (miniActEv () .a) := by
  obtain ⟨m, _, rfl⟩ := (miniature_manifold_iff C f).1 hf
  have h1 : curvePt m (miniSampleEv .a) = nu (fun _ => m) miniature (miniSampleEv .a) := by
    rw [miniature_nu_eq]; rfl
  have h2 : curvePt m (miniActEv () .a) = nu (fun _ => m) miniature (miniActEv () .a) := by
    rw [miniature_nu_eq]; rfl
  rw [h1, h2, miniature_nu_sample, miniature_nu_live]

/-! ## CA-10′'s off-curve state -/

/-- The product state with sample marginal `p` and live marginal `r`:
`X ↦ ∑_{(s,l) ∈ X} p(s) r(l)`. Source: CA-10′ ("the product state with marginals (½, ⅓)").
Kind: D -/
def prodState (p r : ℚ) : Finset MiniW → ℚ := fun X =>
  ∑ w ∈ X, (if w.1 = .a then p else 1 - p) * (if w.2 = .a then r else 1 - r)

/-- The product state's sample marginal is `p`. Source: none: infrastructure. Kind: L -/
theorem prodState_sample (p r : ℚ) : prodState p r (miniSampleEv .a) = p := by
  simp only [prodState, miniSampleEv]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp [Act2.sum_univ]
  ring

/-- The product state's live marginal is `r`. Source: none: infrastructure. Kind: L -/
theorem prodState_live (p r : ℚ) : prodState p r (miniActEv () .a) = r := by
  simp only [prodState, miniActEv]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp [Act2.sum_univ]
  ring

/-- **CA-10′'s off-curve state, confirmed**: the product state with marginals `(½, ⅓)` is on no
point of the manifold, because its marginals differ while every manifold point's agree.
Source: CA-10′ ("the product state with marginals (½, ⅓) is off the curve"); mandate T7(e)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem prodState_half_third_not_mem_manifold (C : Proc Unit (fun _ => Act2) ℚ) :
    prodState (1/2) (1/3) ∉ manifold miniObs C miniature () := fun h => by
  have := manifold_equal_marginals C _ h
  rw [prodState_sample, prodState_live] at this
  norm_num at this

/-! ## The convex hull strictly exceeds the manifold -/

/-- A worldview in the convex hull of two manifold points: `f = t·g + (1−t)·g'` with `g, g'` on
the manifold and `t ∈ [0, 1]`. (Two-point hull; enough for the witness.)
Source: Q2 ("the credal candidate of Appendix B is its convex hull"). Kind: D -/
def InHull2 (C : Proc Unit (fun _ => Act2) ℚ) (f : Finset MiniW → ℚ) : Prop :=
  ∃ t : ℚ, 0 ≤ t ∧ t ≤ 1 ∧ ∃ g g', g ∈ manifold miniObs C miniature () ∧
    g' ∈ manifold miniObs C miniature () ∧ ∀ X, f X = t * g X + (1 - t) * g' X

/-- Two-point hull members have equal marginals too (the marginals are linear).
Source: none: infrastructure. Kind: L -/
theorem inHull2_equal_marginals (C : Proc Unit (fun _ => Act2) ℚ) (f : Finset MiniW → ℚ)
    (hf : InHull2 C f) : f (miniSampleEv .a) = f (miniActEv () .a) := by
  obtain ⟨t, _, _, g, g', hg, hg', hf⟩ := hf
  rw [hf, hf, manifold_equal_marginals C g hg, manifold_equal_marginals C g' hg']

/-- **The product state with marginals `(½, ⅓)` is outside the two-point hull as well**, so it
cannot witness "the convex hull strictly exceeds the manifold" (the mandate's T7(e) pairing;
findings F19). Source: mandate T7(e); Q2. Kind: N+. Fidelity: exact. Hyps: none -/
theorem prodState_half_third_not_in_hull (C : Proc Unit (fun _ => Act2) ℚ) :
    ¬ InHull2 C (prodState (1/2) (1/3)) := fun h => by
  have := inHull2_equal_marginals C _ h
  rw [prodState_sample, prodState_live] at this
  norm_num at this

/-- The self-model `(¼, ¾)`. Source: mandate T7(e) (witness). Kind: D -/
def quarterPt : FinDistr ℚ Act2 := FinDistr.act2 (1/4) (by norm_num) (by norm_num)

/-- The self-model `(¾, ¼)`. Source: mandate T7(e) (witness). Kind: D -/
def threeQuarterPt : FinDistr ℚ Act2 := FinDistr.act2 (3/4) (by norm_num) (by norm_num)

/-- `quarterPt` is full-support. Source: none: infrastructure. Kind: L -/
theorem quarterPt_pos (x : Act2) : 0 < quarterPt.w x := by cases x <;> norm_num [quarterPt, FinDistr.act2]

/-- `threeQuarterPt` is full-support. Source: none: infrastructure. Kind: L -/
theorem threeQuarterPt_pos (x : Act2) : 0 < threeQuarterPt.w x := by
  cases x <;> norm_num [threeQuarterPt, FinDistr.act2]

/-- The midpoint of the curve points at `m = ¼` and `m = ¾`:
`(5/16, 3/16, 3/16, 5/16)`. Source: mandate T7(e) (witness). Kind: D -/
def hullMid : Finset MiniW → ℚ := fun X =>
  (1/2) * curvePt quarterPt X + (1/2) * curvePt threeQuarterPt X

/-- **The convex hull strictly exceeds the manifold on the miniature**: `hullMid` is a convex
combination of two manifold points (`m = ¼`, `m = ¾`) and is on no point of the curve — a curve
point with `f{(a,a)} = 5/16` would need `m(a)² = 5/16`, while `f(sample = a) = ½` forces
`m(a) = ½`. The genuine witness of Q2's "credal candidate ⊋ manifold" on this tree.
Source: Q2 ("the credal candidate of Appendix B is its convex hull"); CA-10′; mandate T7(e)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem miniature_hull_exceeds_manifold (C : Proc Unit (fun _ => Act2) ℚ) :
    InHull2 C hullMid ∧ hullMid ∉ manifold miniObs C miniature () := by
  refine ⟨⟨1/2, by norm_num, by norm_num, curvePt quarterPt, curvePt threeQuarterPt,
    curvePt_mem_manifold C _ quarterPt_pos, curvePt_mem_manifold C _ threeQuarterPt_pos,
    fun X => by simp only [hullMid]; norm_num⟩, fun h => ?_⟩
  obtain ⟨m, _, hm⟩ := (miniature_manifold_iff C _).1 h
  have hsum := m.sum_one
  rw [Act2.sum_univ] at hsum
  have haa := congrFun hm {(Act2.a, Act2.a)}
  have hsa := congrFun hm (miniSampleEv .a)
  simp only [hullMid, curvePt, Finset.sum_singleton] at haa
  simp only [hullMid, curvePt, miniSampleEv] at hsa
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_filter, Fintype.sum_prod_type,
    Finset.sum_filter, Fintype.sum_prod_type] at hsa
  simp [Act2.sum_univ, quarterPt, threeQuarterPt, FinDistr.act2] at haa hsa
  have hb : m.w Act2.b = 1 - m.w Act2.a := by linarith
  rw [hb] at hsa
  have hma : m.w Act2.a = 1 / 2 := by ring_nf at hsa; linarith
  rw [hma] at haa
  norm_num at haa

end Cleanroom.Decision.DpCalibLimits
