/-
# The projection onto a rational polytope, piecewise and rational

`RationalPolytope` gives the nearest point and a certificate for it.  This file gives the
finitely many **rational affine pieces** the nearest point is assembled from, which is what
makes the projection compilable into Logical Induction's expressible features.

The pieces are indexed by *faces*: a base vertex together with a list of further vertices.
On the face spanned by `base` and `base + uⱼ`, the nearest point to `p` is the orthogonal
projection onto the affine span, and solving for its barycentric coefficients is a
**rational** linear system with the Gram matrix of the `uⱼ`.  Mathlib supplies the one fact
that makes this work — `Matrix.det_gram_ne_zero_iff_linearIndependent` — so no new linear
algebra is needed.

Two design points carry most of the weight.

*Cells are defined by the certificate, not by the combinatorics.*  The cell of a face is the
set of `p` at which that face's candidate passes `RationalPolytope.eq_proj_of_vertexSet`.
Such a set is closed because the candidate is continuous, and on it the candidate **is** the
projection by uniqueness.  So faces whose Gram system is degenerate need no special
treatment: their candidate is junk, their cell is where the junk happens to be correct
(usually empty), and nothing has to be proved about which faces are degenerate.

*Coverage needs only one good face per point.*  Writing the projection as a convex
combination of vertices with all coefficients positive over a minimal set makes those
vertices affinely independent, and the variational inequality then forces `p − q` orthogonal
to the face, which is exactly the linear system the candidate solves.

Names are provisional (`AGENTS.md` standard 6).
-/

import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Workspace.Normativity.Contrib.RationalPolytope

namespace Workspace.Normativity.Contrib.PolyhedralProjection

open scoped RealInnerProductSpace
open Workspace.Normativity.Contrib.RationalPolytope

variable {d : ℕ}

/-! ## Rational affine forms -/

/-- An affine form on `d` coordinates with rational data.  Finite data, so it can be an
input to a primitive-recursive evaluator later. -/
structure AffineForm (d : ℕ) where
  /-- The coefficient on each coordinate. -/
  coeff : Fin d → ℚ
  /-- The constant term. -/
  const : ℚ

/-- The real value of an affine form. -/
def AffineForm.eval (a : AffineForm d) (p : Pt d) : ℝ :=
  (a.const : ℝ) + ∑ i, (a.coeff i : ℝ) * p i

lemma AffineForm.continuous_eval (a : AffineForm d) : Continuous a.eval := by
  unfold AffineForm.eval
  exact continuous_const.add (continuous_finsetSum _ fun i _ =>
    continuous_const.mul (PiLp.continuous_apply 2 _ i))

/-! ## Faces

A face is a base vertex and a list of further vertices.  The spanning directions are the
differences. -/

/-- A face of the polytope: a base vertex and finitely many further vertices. -/
structure Face (d : ℕ) where
  /-- The base vertex. -/
  base : Fin d → ℚ
  /-- The remaining vertices of the face. -/
  rest : List (Fin d → ℚ)

namespace Face

variable (F : Face d)

/-- The number of spanning directions. -/
def dim : ℕ := F.rest.length

/-- The spanning directions, over `ℚ`. -/
def dirQ (j : Fin F.dim) : Fin d → ℚ := fun i => (F.rest.get ⟨j.1, j.2⟩) i - F.base i

/-- The spanning directions, as points. -/
def dir (j : Fin F.dim) : Pt d := toPt (F.dirQ j)

/-- The rational Gram matrix of the spanning directions. -/
def gramQ : Matrix (Fin F.dim) (Fin F.dim) ℚ :=
  Matrix.of fun j l => ∑ i, F.dirQ j i * F.dirQ l i

lemma gram_eq_map : Matrix.gram ℝ F.dir = F.gramQ.map (fun q : ℚ => (q : ℝ)) := by
  ext j l
  simp only [Matrix.gram_apply, Matrix.map_apply, gramQ, Matrix.of_apply, dir, toPt]
  rw [PiLp.inner_apply]
  push_cast
  exact Finset.sum_congr rfl fun i _ => by simp [RCLike.inner_apply, mul_comm]

/-- The face is *regular* when its Gram system is invertible — equivalently, when its
spanning directions are linearly independent. -/
def Regular : Prop := IsUnit F.gramQ.det

instance : DecidablePred (fun F : Face d => F.Regular) := fun F => by
  unfold Face.Regular
  exact decidable_of_iff (F.gramQ.det ≠ 0) isUnit_iff_ne_zero.symm

lemma regular_of_linearIndependent (h : LinearIndependent ℝ F.dir) : F.Regular := by
  have hdet : (Matrix.gram ℝ F.dir).det ≠ 0 :=
    Matrix.det_gram_ne_zero_iff_linearIndependent.mpr h
  rw [gram_eq_map] at hdet
  have hmap : ((F.gramQ.det : ℚ) : ℝ)
      = (F.gramQ.map (fun q : ℚ => (q : ℝ))).det := by
    simpa [RingHom.mapMatrix_apply] using RingHom.map_det (Rat.castHom ℝ) F.gramQ
  rw [← hmap] at hdet
  exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hdet)

end Face

end Workspace.Normativity.Contrib.PolyhedralProjection

#print axioms Workspace.Normativity.Contrib.PolyhedralProjection.Face.gram_eq_map
#print axioms Workspace.Normativity.Contrib.PolyhedralProjection.Face.regular_of_linearIndependent
