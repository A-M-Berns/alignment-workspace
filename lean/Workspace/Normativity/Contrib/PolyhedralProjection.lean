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

/-! ## The candidate map of a face

Solving the face's linear system gives an explicit affine map with rational coefficients.
The inverse is written out as `det⁻¹ • adjugate` rather than through `Ring.inverse`, so the
whole thing stays a computable `def`. -/

/-- The inverse of the face's Gram matrix, written so as to stay computable. -/
def gramInvQ : Matrix (Fin F.dim) (Fin F.dim) ℚ :=
  (F.gramQ.det)⁻¹ • F.gramQ.adjugate

lemma gramInvQ_mul (h : F.Regular) : F.gramInvQ * F.gramQ = 1 := by
  have hdet : F.gramQ.det ≠ 0 := isUnit_iff_ne_zero.mp h
  rw [gramInvQ, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul,
    inv_mul_cancel₀ hdet, one_smul]

/-- The `(i, a)` entry of the linear part of the face's candidate map. -/
def coefQ (i a : Fin d) : ℚ :=
  ∑ j, F.dirQ j i * ∑ l, F.gramInvQ j l * F.dirQ l a

/-- The face's candidate affine form for coordinate `i`. -/
def piece (i : Fin d) : AffineForm d where
  coeff := fun a => F.coefQ i a
  const := F.base i - ∑ a, F.coefQ i a * F.base a

/-- The face's candidate point: the coordinatewise value of its pieces. -/
def candidate (p : Pt d) : Pt d := WithLp.toLp 2 fun i => (F.piece i).eval p

lemma candidate_apply (p : Pt d) (i : Fin d) :
    (F.candidate p) i = (F.piece i).eval p := rfl

lemma continuous_candidate : Continuous F.candidate := by
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => (F.piece i).continuous_eval)

/-! ## The candidate solves the face's Gram system -/

/-- The right-hand side of the face's linear system at `p`. -/
def rhs (p : Pt d) (l : Fin F.dim) : ℝ :=
  ∑ a, (F.dirQ l a : ℝ) * (p a - (F.base a : ℝ))

/-- The barycentric coefficients the candidate uses. -/
def coord (p : Pt d) (j : Fin F.dim) : ℝ :=
  ∑ l, (F.gramInvQ j l : ℝ) * F.rhs p l

lemma rhs_eq_inner (p : Pt d) (l : Fin F.dim) :
    F.rhs p l = ⟪F.dir l, p - toPt F.base⟫ := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [RCLike.inner_apply, dir, toPt, WithLp.ofLp_toLp, PiLp.sub_apply,
    starRingEnd_apply, star_trivial]
  ring

/-- The candidate, written through its barycentric coefficients. -/
lemma candidate_apply_eq (p : Pt d) (i : Fin d) :
    (F.candidate p) i = (F.base i : ℝ) + ∑ j, (F.dirQ j i : ℝ) * F.coord p j := by
  have hsplit : ∑ a, (F.coefQ i a : ℝ) * (p a - (F.base a : ℝ))
      = ∑ a, (F.coefQ i a : ℝ) * p a - ∑ a, (F.coefQ i a : ℝ) * (F.base a : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hL : ∑ a, (F.coefQ i a : ℝ) * (p a - (F.base a : ℝ))
      = ∑ a, ∑ j, ∑ l,
        ((F.dirQ j i : ℝ) * (F.gramInvQ j l : ℝ) * (F.dirQ l a : ℝ))
          * (p a - (F.base a : ℝ)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [coefQ]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hR : ∑ j, (F.dirQ j i : ℝ) * F.coord p j
      = ∑ j, ∑ l, ∑ a,
        ((F.dirQ j i : ℝ) * (F.gramInvQ j l : ℝ) * (F.dirQ l a : ℝ))
          * (p a - (F.base a : ℝ)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [coord, rhs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact Finset.sum_congr rfl fun a _ => by ring
  have hmain : ∑ a, (F.coefQ i a : ℝ) * (p a - (F.base a : ℝ))
      = ∑ j, (F.dirQ j i : ℝ) * F.coord p j := by
    rw [hL, hR, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Finset.sum_comm
  rw [candidate_apply, piece, AffineForm.eval]
  push_cast
  linarith [hsplit, hmain]

/-! ## Uniqueness: the candidate is the only solution of the face's system -/

lemma inner_dir (l j : Fin F.dim) : ⟪F.dir l, F.dir j⟫ = (F.gramQ l j : ℝ) := by
  rw [PiLp.inner_apply]
  simp only [gramQ, Matrix.of_apply]
  push_cast
  exact Finset.sum_congr rfl fun i _ => by
    simp only [RCLike.inner_apply, dir, toPt, WithLp.ofLp_toLp, starRingEnd_apply,
      star_trivial]
    ring

lemma gramInv_mul_gram (h : F.Regular) (j k : Fin F.dim) :
    ∑ l, F.gramInvQ j l * F.gramQ l k = if j = k then 1 else 0 := by
  have hone : (F.gramInvQ * F.gramQ) j k
      = (1 : Matrix (Fin F.dim) (Fin F.dim) ℚ) j k := by rw [F.gramInvQ_mul h]
  rwa [Matrix.mul_apply, Matrix.one_apply] at hone

lemma gramInv_mul_gram_real (h : F.Regular) (j k : Fin F.dim) :
    ∑ l, (F.gramInvQ j l : ℝ) * (F.gramQ l k : ℝ) = if j = k then (1 : ℝ) else 0 := by
  have hq := F.gramInv_mul_gram h j k
  have hcast : ((∑ l, F.gramInvQ j l * F.gramQ l k : ℚ) : ℝ)
      = ∑ l, (F.gramInvQ j l : ℝ) * (F.gramQ l k : ℝ) := by push_cast; ring
  split_ifs with hjk
  · rw [if_pos hjk] at hq
    rw [← hcast, hq]; norm_num
  · rw [if_neg hjk] at hq
    rw [← hcast, hq]; norm_num

/-- **Uniqueness.**  A point of the face's affine span whose displacement from `p` is
orthogonal to the face is the candidate.  This is the only place the Gram inverse is used,
and the only place regularity is needed. -/
theorem candidate_unique (h : F.Regular) (p x : Pt d) (c : Fin F.dim → ℝ)
    (hx : ∀ i, x i = (F.base i : ℝ) + ∑ j, (F.dirQ j i : ℝ) * c j)
    (horth : ∀ l, ⟪F.dir l, p - x⟫ = 0) :
    x = F.candidate p := by
  have hxb : ∀ l, ⟪F.dir l, x - toPt F.base⟫ = ∑ j, c j * (F.gramQ l j : ℝ) := by
    intro l
    have hL : ⟪F.dir l, x - toPt F.base⟫
        = ∑ i, (F.dirQ l i : ℝ) * ∑ j, (F.dirQ j i : ℝ) * c j := by
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [RCLike.inner_apply, dir, toPt, WithLp.ofLp_toLp, PiLp.sub_apply,
        starRingEnd_apply, star_trivial, hx i]
      ring
    have hR : ∑ j, c j * (F.gramQ l j : ℝ)
        = ∑ j, ∑ i, c j * ((F.dirQ l i : ℝ) * (F.dirQ j i : ℝ)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [gramQ, Matrix.of_apply]
      push_cast
      rw [Finset.mul_sum]
      try exact Finset.sum_congr rfl fun i _ => by ring
    rw [hL, hR, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hrhs : ∀ l, F.rhs p l = ∑ j, c j * (F.gramQ l j : ℝ) := by
    intro l
    rw [F.rhs_eq_inner p l, ← hxb l]
    have hdec : (p : Pt d) - toPt F.base = (p - x) + (x - toPt F.base) := by abel
    rw [hdec, inner_add_right, horth l, zero_add]
  have hcoord : ∀ j, F.coord p j = c j := by
    intro j
    simp only [coord, hrhs]
    have hswap : ∑ l, (F.gramInvQ j l : ℝ) * ∑ k, c k * (F.gramQ l k : ℝ)
        = ∑ k, c k * ∑ l, (F.gramInvQ j l : ℝ) * (F.gramQ l k : ℝ) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    rw [hswap]
    simp only [F.gramInv_mul_gram_real h]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk; simp [Ne.symm hk]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  ext i
  rw [hx i, F.candidate_apply_eq p i]
  exact congrArg _ (Finset.sum_congr rfl fun j _ => by rw [hcoord j])

end Face


/-! ## Orthogonality on the active set

If the projection is a convex combination of vertices, then the directions between any two
vertices carrying **positive** weight are orthogonal to `p − proj p`: shifting a little
weight from one to the other stays inside the region, and the variational inequality then
bites in both directions.  This is the whole geometric content of coverage. -/

/-- Shifting weight `t` from `z` to `y` moves a convex combination by `t • (y - z)`. -/
private lemma sum_update_shift (Vf : Finset (Pt d)) (w : Pt d → ℝ) (y z : Pt d)
    (hy : y ∈ Vf) (hz : z ∈ Vf) (hyz : y ≠ z) (t : ℝ) :
    ∑ v ∈ Vf, (if v = y then w v + t else if v = z then w v - t else w v) • v
      = (∑ v ∈ Vf, w v • v) + t • (y - z) := by
  classical
  have hpt : ∀ v ∈ Vf,
      (if v = y then w v + t else if v = z then w v - t else w v) • v
        = w v • v + ((if v = y then t else 0) • v - (if v = z then t else 0) • v) := by
    intro v _
    by_cases hvy : v = y
    · subst hvy
      rw [if_pos rfl, if_pos rfl, if_neg hyz]
      module
    · by_cases hvz : v = z
      · subst hvz
        rw [if_neg hvy, if_pos rfl, if_neg hvy, if_pos rfl]
        module
      · rw [if_neg hvy, if_neg hvz, if_neg hvy, if_neg hvz]
        module
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h1 : ∑ v ∈ Vf, (if v = y then t else 0) • v = t • y := by
    rw [Finset.sum_eq_single y]
    · rw [if_pos rfl]
    · intro b _ hb; rw [if_neg hb, zero_smul]
    · intro hy'; exact absurd hy hy'
  have h2 : ∑ v ∈ Vf, (if v = z then t else 0) • v = t • z := by
    rw [Finset.sum_eq_single z]
    · rw [if_pos rfl]
    · intro b _ hb; rw [if_neg hb, zero_smul]
    · intro hz'; exact absurd hz hz'
  rw [h1, h2, smul_sub]

/-- The perturbed combination is still in the region. -/
private lemma shifted_mem_carrier (K : RationalPolytope d) {w : Pt d → ℝ}
    (hw : ∀ v ∈ K.vertexSet, 0 ≤ w v)
    (hsum : ∑ v ∈ K.vertexSet_finite.toFinset, w v = 1)
    {y z : Pt d} (hy : y ∈ K.vertexSet_finite.toFinset)
    (hz : z ∈ K.vertexSet_finite.toFinset) (hyz : y ≠ z) {t : ℝ} (ht0 : 0 ≤ t)
    (htz : t ≤ w z) :
    (∑ v ∈ K.vertexSet_finite.toFinset, w v • v) + t • (y - z) ∈ K.carrier := by
  classical
  have hnonneg : ∀ v ∈ K.vertexSet,
      0 ≤ (if v = y then w v + t else if v = z then w v - t else w v) := by
    intro v hv
    have hbase := hw v hv
    by_cases hvy : v = y
    · rw [if_pos hvy]; linarith
    · rw [if_neg hvy]
      by_cases hvz : v = z
      · subst hvz; rw [if_pos rfl]; linarith
      · rw [if_neg hvz]; exact hbase
  have hsum' : ∑ v ∈ K.vertexSet_finite.toFinset,
      (if v = y then w v + t else if v = z then w v - t else w v) = 1 := by
    have hpt : ∀ v ∈ K.vertexSet_finite.toFinset,
        (if v = y then w v + t else if v = z then w v - t else w v)
          = w v + ((if v = y then t else 0) - (if v = z then t else 0)) := by
      intro v _
      by_cases hvy : v = y
      · subst hvy
        rw [if_pos rfl, if_pos rfl, if_neg hyz]; ring
      · by_cases hvz : v = z
        · subst hvz
          rw [if_neg hvy, if_pos rfl, if_neg hvy, if_pos rfl]; ring
        · rw [if_neg hvy, if_neg hvz, if_neg hvy, if_neg hvz]; ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, hsum, Finset.sum_sub_distrib]
    have e1 : ∑ v ∈ K.vertexSet_finite.toFinset, (if v = y then t else 0) = t := by
      rw [Finset.sum_eq_single y]
      · rw [if_pos rfl]
      · intro b _ hb; rw [if_neg hb]
      · intro hy'; exact absurd hy hy'
    have e2 : ∑ v ∈ K.vertexSet_finite.toFinset, (if v = z then t else 0) = t := by
      rw [Finset.sum_eq_single z]
      · rw [if_pos rfl]
      · intro b _ hb; rw [if_neg hb]
      · intro hz'; exact absurd hz hz'
    rw [e1, e2, sub_self, add_zero]
  have hmem : (∑ v ∈ K.vertexSet_finite.toFinset, w v • v) + t • (y - z)
      ∈ convexHull ℝ K.vertexSet := by
    rw [K.vertexSet_finite.convexHull_eq]
    refine ⟨fun v => if v = y then w v + t else if v = z then w v - t else w v,
      hnonneg, hsum', ?_⟩
    rw [Finset.centerMass_eq_of_sum_1 _ _ hsum']
    exact sum_update_shift _ w y z hy hz hyz t
  exact hmem

/-- **Orthogonality on the active set.** -/
theorem inner_eq_zero_of_active (K : RationalPolytope d) (p : Pt d) {w : Pt d → ℝ}
    (hw : ∀ v ∈ K.vertexSet, 0 ≤ w v)
    (hsum : ∑ v ∈ K.vertexSet_finite.toFinset, w v = 1)
    (hq : ∑ v ∈ K.vertexSet_finite.toFinset, w v • v = K.proj p)
    {y z : Pt d} (hy : y ∈ K.vertexSet_finite.toFinset)
    (hz : z ∈ K.vertexSet_finite.toFinset) (hwy : 0 < w y) (hwz : 0 < w z) :
    ⟪p - K.proj p, y - z⟫ = 0 := by
  classical
  by_cases hyz : y = z
  · subst hyz; simp
  have key : ∀ a b : Pt d, a ∈ K.vertexSet_finite.toFinset →
      b ∈ K.vertexSet_finite.toFinset → a ≠ b → 0 < w b →
      ⟪p - K.proj p, a - b⟫ ≤ 0 := by
    intro a b ha hb hab hwb
    have hmem := shifted_mem_carrier K hw hsum ha hb hab (le_of_lt hwb) (le_refl (w b))
    rw [hq] at hmem
    have hvi := K.proj_variational p hmem
    rw [add_sub_cancel_left, real_inner_smul_right] at hvi
    nlinarith [hvi, hwb]
  have h1 := key y z hy hz hyz hwz
  have h2 := key z y hz hy (Ne.symm hyz) hwy
  have hflip : (z : Pt d) - y = -(y - z) := by abel
  rw [hflip, inner_neg_right] at h2
  linarith

/-! ## Cells

The cell of a face is where its candidate passes the polytope's own nearest-point
certificate.  Correctness on the cell is then immediate from uniqueness, and no fact about
which faces are degenerate is ever needed. -/

/-- The cell of a face: the points at which its candidate is certified as the nearest
point. -/
def cell (K : RationalPolytope d) (F : Face d) : Set (Pt d) :=
  {p | F.candidate p ∈ K.carrier ∧
    ∀ v ∈ K.vertexSet, ⟪p - F.candidate p, v - F.candidate p⟫ ≤ 0}

/-- On its cell, a face's candidate **is** the projection. -/
theorem candidate_eq_proj_of_mem_cell (K : RationalPolytope d) (F : Face d) {p : Pt d}
    (hp : p ∈ cell K F) : F.candidate p = K.proj p :=
  K.eq_proj_of_vertexSet hp.1 hp.2

lemma isClosed_cell (K : RationalPolytope d) (F : Face d) : IsClosed (cell K F) := by
  have hc := F.continuous_candidate
  have h1 : IsClosed {p : Pt d | F.candidate p ∈ K.carrier} :=
    K.carrier_isCompact.isClosed.preimage hc
  have h2 : ∀ v ∈ K.vertexSet,
      IsClosed {p : Pt d | ⟪p - F.candidate p, v - F.candidate p⟫ ≤ 0} := by
    intro v _
    have : Continuous fun p : Pt d => ⟪p - F.candidate p, v - F.candidate p⟫ :=
      continuous_inner.comp ((continuous_id.sub hc).prodMk (continuous_const.sub hc))
    exact isClosed_le this continuous_const
  have hEq : cell K F = {p : Pt d | F.candidate p ∈ K.carrier} ∩
      ⋂ v ∈ K.vertexSet, {p : Pt d | ⟪p - F.candidate p, v - F.candidate p⟫ ≤ 0} := by
    ext p
    simp only [cell, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hEq]
  exact h1.inter (isClosed_biInter h2)


end Workspace.Normativity.Contrib.PolyhedralProjection

#print axioms Workspace.Normativity.Contrib.PolyhedralProjection.Face.gram_eq_map
#print axioms Workspace.Normativity.Contrib.PolyhedralProjection.Face.regular_of_linearIndependent
#print axioms Workspace.Normativity.Contrib.PolyhedralProjection.Face.gramInvQ_mul
#print axioms Workspace.Normativity.Contrib.PolyhedralProjection.Face.candidate_apply_eq
#print axioms Workspace.Normativity.Contrib.PolyhedralProjection.Face.candidate_unique
#print axioms Workspace.Normativity.Contrib.PolyhedralProjection.inner_eq_zero_of_active
#print axioms Workspace.Normativity.Contrib.PolyhedralProjection.candidate_eq_proj_of_mem_cell
#print axioms Workspace.Normativity.Contrib.PolyhedralProjection.isClosed_cell
