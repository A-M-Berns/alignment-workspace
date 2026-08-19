/-
# Rational polytopes and their Euclidean projection

The quantitative constraint the enforcement trader acts on is a polytope with rational
data.  This file fixes the representation and proves the two facts everything downstream
needs about the nearest point: that it exists and is unique, and that membership plus a
finite inequality **against the vertices alone** certifies it.

**The representation is by vertices, not by inequalities.**  That is a deliberate choice
and it pays for itself twice.  The region the deductive specialisation actually wants is
`conv {W|_Φ : W ∈ PC(D)}` — a convex hull of finitely many `{0,1}` points — so a vertex
list is what that construction already produces and no facet enumeration is ever needed.
And the nearest-point certificate reduces to the vertices by nothing more than convexity of
a half-space, where the inequality description would need the normal-cone decomposition and
so a Farkas argument.

`proj` is `noncomputable`, and that is not a defect: it is the mathematical object.  What
has to be computable is the finite list of affine *pieces* that agree with it, which is the
next file.

Names are provisional (`AGENTS.md` standard 6).
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Caratheodory

namespace Workspace.Normativity.Contrib.RationalPolytope

open scoped RealInnerProductSpace

variable {d : ℕ}

/-- The ambient fragment space: `d` real coordinates with the Euclidean inner product. -/
abbrev Pt (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- A rational point, as a point of the ambient space. -/
def toPt (v : Fin d → ℚ) : Pt d := WithLp.toLp 2 (fun i => (v i : ℝ))

/-- A polytope presented by a nonempty finite list of rational vertices. -/
structure _root_.RationalPolytope (d : ℕ) where
  /-- The vertices, with rational coordinates. -/
  verts : List (Fin d → ℚ)
  /-- At least one vertex, so the region is nonempty. -/
  verts_ne : verts ≠ []

end Workspace.Normativity.Contrib.RationalPolytope

namespace RationalPolytope

open scoped RealInnerProductSpace
open Workspace.Normativity.Contrib.RationalPolytope

variable {d : ℕ}

/-- The vertices as points of the ambient space. -/
def vertexSet (K : RationalPolytope d) : Set (Pt d) := toPt '' {v | v ∈ K.verts}

/-- The region: the convex hull of the vertices. -/
def carrier (K : RationalPolytope d) : Set (Pt d) := convexHull ℝ K.vertexSet

lemma vertexSet_finite (K : RationalPolytope d) : K.vertexSet.Finite :=
  (K.verts.finite_toSet).image _

lemma vertexSet_nonempty (K : RationalPolytope d) : K.vertexSet.Nonempty := by
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil K.verts K.verts_ne
  exact ⟨toPt v, ⟨v, hv, rfl⟩⟩

lemma vertexSet_subset_carrier (K : RationalPolytope d) : K.vertexSet ⊆ K.carrier :=
  subset_convexHull ℝ _

lemma carrier_convex (K : RationalPolytope d) : Convex ℝ K.carrier :=
  convex_convexHull ℝ _

lemma carrier_nonempty (K : RationalPolytope d) : K.carrier.Nonempty :=
  K.vertexSet_nonempty.mono K.vertexSet_subset_carrier

lemma carrier_isCompact (K : RationalPolytope d) : IsCompact K.carrier :=
  K.vertexSet_finite.isCompact_convexHull ℝ

lemma carrier_isComplete (K : RationalPolytope d) : IsComplete K.carrier :=
  K.carrier_isCompact.isComplete

/-! ## The nearest point -/

lemma exists_nearest (K : RationalPolytope d) (p : Pt d) :
    ∃ q ∈ K.carrier, ‖p - q‖ = ⨅ w : K.carrier, ‖p - w‖ :=
  exists_norm_eq_iInf_of_complete_convex K.carrier_nonempty K.carrier_isComplete
    K.carrier_convex p

/-- The Euclidean nearest point of the region to `p`.  Noncomputable by construction — it
is the mathematical object; the computable content is the finite list of affine pieces that
agree with it. -/
noncomputable def proj (K : RationalPolytope d) (p : Pt d) : Pt d :=
  (K.exists_nearest p).choose

lemma proj_mem (K : RationalPolytope d) (p : Pt d) : K.proj p ∈ K.carrier :=
  (K.exists_nearest p).choose_spec.1

lemma proj_norm_eq_iInf (K : RationalPolytope d) (p : Pt d) :
    ‖p - K.proj p‖ = ⨅ w : K.carrier, ‖p - w‖ :=
  (K.exists_nearest p).choose_spec.2

/-- **The variational inequality.**  The defining property, at every point of the region. -/
theorem proj_variational (K : RationalPolytope d) (p : Pt d) {y : Pt d}
    (hy : y ∈ K.carrier) : ⟪p - K.proj p, y - K.proj p⟫ ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero K.carrier_convex (K.proj_mem p)).mp
    (K.proj_norm_eq_iInf p) y hy

/-! ## The vertex certificate

The half-space `{y : ⟪p − q, y − q⟫ ≤ 0}` is convex, so checking the inequality at the
vertices checks it on the whole hull.  This is what replaces a normal-cone/Farkas argument,
and it is the reason the vertex representation was chosen. -/

/-- The inequality against the vertices already gives it against the whole region. -/
theorem forall_carrier_of_forall_vertexSet (K : RationalPolytope d) {p q : Pt d}
    (h : ∀ v ∈ K.vertexSet, ⟪p - q, v - q⟫ ≤ 0) :
    ∀ y ∈ K.carrier, ⟪p - q, y - q⟫ ≤ 0 := by
  have hlin : IsLinearMap ℝ (fun y : Pt d => ⟪p - q, y⟫) :=
    { map_add := fun x y => inner_add_right _ _ _
      map_smul := fun c x => real_inner_smul_right _ _ _ }
  have hconv : Convex ℝ {y : Pt d | ⟪p - q, y - q⟫ ≤ 0} := by
    have hset : {y : Pt d | ⟪p - q, y - q⟫ ≤ 0}
        = {y : Pt d | (fun z : Pt d => ⟪p - q, z⟫) y ≤ ⟪p - q, q⟫} := by
      ext y
      simp only [Set.mem_setOf_eq, inner_sub_right]
      constructor <;> intro h' <;> linarith
    rw [hset]
    exact convex_halfSpace_le hlin _
  intro y hy
  exact convexHull_min h hconv hy

/-- **The certificate.**  A point of the region satisfying the vertex inequalities *is* the
nearest point.  Uniqueness of the nearest point is what makes this an identification rather
than merely a sufficient condition. -/
theorem eq_proj_of_vertexSet (K : RationalPolytope d) {p q : Pt d}
    (hq : q ∈ K.carrier) (h : ∀ v ∈ K.vertexSet, ⟪p - q, v - q⟫ ≤ 0) :
    q = K.proj p := by
  have hall := K.forall_carrier_of_forall_vertexSet h
  have h1 : ‖p - q‖ = ⨅ w : K.carrier, ‖p - w‖ :=
    (norm_eq_iInf_iff_real_inner_le_zero K.carrier_convex hq).mpr hall
  have h2 := K.proj_norm_eq_iInf p
  -- two minimisers of a strictly convex problem coincide
  have hqp := hall _ (K.proj_mem p)
  have hpq := K.proj_variational p hq
  have : ‖q - K.proj p‖ ^ 2 ≤ 0 := by
    have hexp : ‖q - K.proj p‖ ^ 2
        = ⟪p - K.proj p, q - K.proj p⟫ - ⟪p - q, q - K.proj p⟫ := by
      rw [← inner_sub_left]
      have : p - K.proj p - (p - q) = q - K.proj p := by abel
      rw [this, real_inner_self_eq_norm_sq]
    rw [hexp]
    have hneg : ⟪p - q, q - K.proj p⟫ ≥ 0 := by
      have : ⟪p - q, K.proj p - q⟫ ≤ 0 := hqp
      have hflip : (K.proj p - q : Pt d) = -(q - K.proj p) := by abel
      rw [hflip, inner_neg_right] at this
      linarith
    linarith [hpq]
  have : ‖q - K.proj p‖ = 0 := by
    nlinarith [norm_nonneg (q - K.proj p)]
  have := sub_eq_zero.mp (norm_eq_zero.mp this)
  exact this

/-- The region lies in the unit cube exactly when its vertices do. -/
theorem carrier_mem_cube (K : RationalPolytope d)
    (hv : ∀ v ∈ K.verts, ∀ i, 0 ≤ v i ∧ v i ≤ 1) {y : Pt d} (hy : y ∈ K.carrier) (i : Fin d) :
    0 ≤ y i ∧ y i ≤ 1 := by
  have hbox : Convex ℝ {x : Pt d | 0 ≤ x i ∧ x i ≤ 1} := by
    have hlin : IsLinearMap ℝ (fun x : Pt d => x i) :=
      { map_add := fun x y => rfl, map_smul := fun c x => rfl }
    exact (convex_halfSpace_ge hlin 0).inter (convex_halfSpace_le hlin 1)
  refine convexHull_min ?_ hbox hy
  rintro x ⟨v, hv', rfl⟩
  obtain ⟨h0, h1⟩ := hv v hv' i
  have e : (toPt v).ofLp i = ((v i : ℚ) : ℝ) := rfl
  refine ⟨?_, ?_⟩
  · show (0 : ℝ) ≤ (toPt v).ofLp i
    rw [e]
    calc (0 : ℝ) = ((0 : ℚ) : ℝ) := by norm_num
      _ ≤ ((v i : ℚ) : ℝ) := by exact_mod_cast h0
  · show (toPt v).ofLp i ≤ (1 : ℝ)
    rw [e]
    calc ((v i : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := by exact_mod_cast h1
      _ = 1 := by norm_num

end RationalPolytope

#print axioms RationalPolytope.proj_mem
#print axioms RationalPolytope.proj_variational
#print axioms RationalPolytope.forall_carrier_of_forall_vertexSet
#print axioms RationalPolytope.eq_proj_of_vertexSet
#print axioms RationalPolytope.carrier_mem_cube
