/-
# The projector's max–min representation, in the compiler's coordinates

`PolyhedralCoverage.exists_maxMin_proj` writes each coordinate of the Euclidean projector
onto a rational polytope as a `Finset.sup'` of `Finset.inf'`s of rational affine forms,
indexed by `Fin d` and by finite sets of face positions.  `ProjectionCompiler` consumes a
`Rep`: a nonempty list of nonempty lists of positionally-aligned rational data, evaluated
by `List.foldr max` of `List.foldr min`, over the sentences a `Fragment` prices.  One
mathematical object, three mismatches — the coordinate index, the shape of the affine data,
and the fold — and this file removes all three.

**The index bridge is `restrict`**, which reads a price vector as a point of
`Pt F.coords.length` through the fragment's own coordinate list.  Prices off the fragment
are not assumed to be anything: the compiler's `AffineForm.coeff` is `0` outside
`F.coords`, and the geometry never sees them.

**The affine bridge is `ofGeom`**, `List.ofFn` on the coefficient family.  Its correctness,
`evalR_ofGeom`, is where the fragment's `Nodup` is spent.  The compiler sums over
`F.toFinset` and the geometry over `Fin F.coords.length`; `sum_toFinset_eq_sum_fin` moves
the first to the second, and there positional lookup is the identity,
`F.coords.idxOf (F.coords.get k) = k`, which is exactly what duplicate-freeness buys.

**The fold bridge** is `foldr_min_eq_inf'` and its `max`/`sup'` dual, each an induction on
the list.  A nonempty `Finset` reaches a `Group` or a `Rep` through `Finset.toList`, whose
`toFinset` is the set it came from.

The payoff is `exists_repMap`: for a fragment `F` and a rational polytope in
`F.coords.length` dimensions there is one `Rep` per priced sentence whose `repEval` is that
sentence's coordinate of the projection, at every price vector.  That is the hypothesis
`ProjectionCompiler.projectionStrategy_realizes` takes as given.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.PolyhedralCoverage
import Workspace.Normativity.Contrib.ProjectionCompiler

namespace Workspace.Normativity.Contrib.ProjectionBridge

open LogicalInduction (Sentence)
open Workspace.Normativity.Contrib.RationalPolytope
open Workspace.Normativity.Contrib.ProjectionCompiler (Fragment groupEval repEval)

/-! ## The index bridge

A price vector is a function on all sentences; a point of the geometry is a function on
`Fin F.coords.length`.  The fragment's coordinate list is the dictionary. -/

/-- A price vector, read as a point of the fragment's coordinate space. -/
def restrict (F : Fragment) (p : Sentence → ℝ) : Pt F.coords.length :=
  WithLp.toLp 2 fun k => p (F.coords.get k)

theorem restrict_apply (F : Fragment) (p : Sentence → ℝ) (k : Fin F.coords.length) :
    restrict F p k = p (F.coords.get k) := rfl

/-! ## Affine forms

The geometry's `AffineForm` is a function on `Fin d` plus a constant; the compiler's is a
list of coefficients aligned with `F.coords` plus a constant.  `List.ofFn` converts, and
the two evaluations agree at every price vector. -/

/-- A geometric affine form, as one of the compiler's. -/
def ofGeom {F : Fragment} (a : PolyhedralProjection.AffineForm F.coords.length) :
    ProjectionCompiler.AffineForm :=
  (List.ofFn a.coeff, a.const)

theorem coeff_ofGeom (F : Fragment) (a : PolyhedralProjection.AffineForm F.coords.length)
    (k : Fin F.coords.length) :
    ProjectionCompiler.AffineForm.coeff F (ofGeom a) (F.coords.get k) = a.coeff k := by
  have hlt : (k : ℕ) < (List.ofFn a.coeff).length := by simp
  rw [ProjectionCompiler.AffineForm.coeff, ofGeom, List.get_idxOf F.nodup k,
    List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]

/-- **The affine bridge is correct.**  The compiler's evaluation of the converted form at a
price vector is the geometry's evaluation of the original at the restricted point. -/
theorem evalR_ofGeom (F : Fragment) (a : PolyhedralProjection.AffineForm F.coords.length)
    (p : Sentence → ℝ) :
    ProjectionCompiler.AffineForm.evalR F (ofGeom a) p = a.eval (restrict F p) := by
  classical
  rw [ProjectionCompiler.AffineForm.evalR, PolyhedralProjection.AffineForm.eval,
    ProjectionCompiler.Fragment.toFinset,
    PolyhedralCoverage.sum_toFinset_eq_sum_fin F.coords F.nodup
      fun φ => ((ProjectionCompiler.AffineForm.coeff F (ofGeom a) φ : ℚ) : ℝ) * p φ]
  refine congrArg₂ _ rfl (Finset.sum_congr rfl fun k _ => ?_)
  rw [coeff_ofGeom, restrict_apply]

/-! ## Folds and lattice folds

The compiler folds `min` and `max` over nonempty lists; the geometry takes `Finset.inf'`
and `Finset.sup'`.  Both inductions are on the list, with the head kept general so the step
can move it past the new element. -/

private theorem toFinset_nonempty {ι : Type*} [DecidableEq ι] {l : List ι} (h : l ≠ []) :
    l.toFinset.Nonempty := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l => exact ⟨a, by simp⟩

private theorem toList_ne_nil {ι : Type*} [DecidableEq ι] {s : Finset ι} (h : s.Nonempty) :
    s.toList ≠ [] := fun hc => h.ne_empty (Finset.toList_eq_nil.mp hc)

theorem foldr_min_eq_inf' {ι : Type*} [DecidableEq ι] (f : ι → ℝ) :
    ∀ (a : ι) (l : List ι) (h : ((a :: l).toFinset).Nonempty),
      (l.map f).foldr min (f a) = ((a :: l).toFinset).inf' h f := by
  intro a l
  induction l generalizing a with
  | nil => intro h; simp
  | cons b l ih =>
      intro h
      have h₁ : ((a :: l).toFinset).Nonempty := ⟨a, by simp⟩
      have hset : ((a :: b :: l).toFinset) = insert b ((a :: l).toFinset) := by
        simp only [List.toFinset_cons]
        exact Finset.insert_comm a b l.toFinset
      rw [List.map_cons, List.foldr_cons, ih a h₁]
      simp only [hset]
      rw [Finset.inf'_insert h₁]

theorem foldr_max_eq_sup' {ι : Type*} [DecidableEq ι] (f : ι → ℝ) :
    ∀ (a : ι) (l : List ι) (h : ((a :: l).toFinset).Nonempty),
      (l.map f).foldr max (f a) = ((a :: l).toFinset).sup' h f := by
  intro a l
  induction l generalizing a with
  | nil => intro h; simp
  | cons b l ih =>
      intro h
      have h₁ : ((a :: l).toFinset).Nonempty := ⟨a, by simp⟩
      have hset : ((a :: b :: l).toFinset) = insert b ((a :: l).toFinset) := by
        simp only [List.toFinset_cons]
        exact Finset.insert_comm a b l.toFinset
      rw [List.map_cons, List.foldr_cons, ih a h₁]
      simp only [hset]
      rw [Finset.sup'_insert h₁]

/-! ## Nonempty lists, as groups and representations

`Group` and `Rep` are "one element, then a list": the head carries the fold's seed.  A
nonempty list of indices supplies both. -/

/-- A nonempty list of affine forms, indexed, as a group to minimise over. -/
def groupOf {ι : Type*} (A : ι → ProjectionCompiler.AffineForm) (l : List ι) (h : l ≠ []) :
    ProjectionCompiler.Group :=
  (A (l.head h), l.tail.map A)

/-- A nonempty list of groups, indexed, as a representation to maximise over. -/
def repOf {ι : Type*} (G : ι → ProjectionCompiler.Group) (l : List ι) (h : l ≠ []) :
    ProjectionCompiler.Rep :=
  (G (l.head h), l.tail.map G)

theorem groupEval_groupOf (F : Fragment) {ι : Type*} [DecidableEq ι]
    (A : ι → ProjectionCompiler.AffineForm) (l : List ι) (h : l ≠ [])
    (hne : l.toFinset.Nonempty) (p : Sentence → ℝ) :
    groupEval F (groupOf A l h) p
      = l.toFinset.inf' hne fun i => ProjectionCompiler.AffineForm.evalR F (A i) p := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l =>
      show ((l.map A).map fun x => ProjectionCompiler.AffineForm.evalR F x p).foldr min
          (ProjectionCompiler.AffineForm.evalR F (A a) p) = _
      rw [List.map_map]
      exact foldr_min_eq_inf'
        (fun i => ProjectionCompiler.AffineForm.evalR F (A i) p) a l hne

theorem repEval_repOf (F : Fragment) {ι : Type*} [DecidableEq ι]
    (G : ι → ProjectionCompiler.Group) (l : List ι) (h : l ≠ [])
    (hne : l.toFinset.Nonempty) (p : Sentence → ℝ) :
    repEval F (repOf G l h) p = l.toFinset.sup' hne fun i => groupEval F (G i) p := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l =>
      show ((l.map G).map fun g => groupEval F g p).foldr max (groupEval F (G a) p) = _
      rw [List.map_map]
      exact foldr_max_eq_sup' (fun i => groupEval F (G i) p) a l hne

/-! ## The payoff

`exists_maxMin_proj` supplies the outer index set `Fin (m + 1)` and the inner sets of face
positions; `Finset.toList` turns each into the nonempty list a `Group` or a `Rep` needs, and
the three bridges above make the two evaluations the same number. -/

/-- **One coordinate.**  Each coordinate of the projection onto a rational polytope is the
`repEval` of a representation the compiler accepts, at every price vector. -/
theorem exists_rep_repEval (F : Fragment) (K : RationalPolytope F.coords.length)
    (k : Fin F.coords.length) :
    ∃ r : ProjectionCompiler.Rep, ∀ p : Sentence → ℝ,
      repEval F r p = K.proj (restrict F p) k := by
  classical
  obtain ⟨m, S, hS, hrep⟩ := PolyhedralCoverage.exists_maxMin_proj K k
  set A : Fin (PolyhedralCoverage.faceList K).length → ProjectionCompiler.AffineForm :=
    fun l => ofGeom (((PolyhedralCoverage.faceList K).get l).piece k) with hA
  set G : Fin (m + 1) → ProjectionCompiler.Group :=
    fun j => groupOf A (S j).toList (toList_ne_nil (hS j)) with hG
  refine ⟨repOf G Finset.univ.toList (toList_ne_nil Finset.univ_nonempty), fun p => ?_⟩
  rw [repEval_repOf F G _ _ (toFinset_nonempty (toList_ne_nil Finset.univ_nonempty)) p,
    hrep (restrict F p)]
  refine Finset.sup'_congr _ (Finset.toList_toFinset _) fun j _ => ?_
  rw [hG, groupEval_groupOf F A (S j).toList (toList_ne_nil (hS j))
    (toFinset_nonempty (toList_ne_nil (hS j))) p]
  refine Finset.inf'_congr _ (Finset.toList_toFinset _) fun l _ => ?_
  rw [hA, evalR_ofGeom]

/-- **One representation per priced sentence.**  The map is total on `Sentence`; its values
are correct at the priced ones, which is what the compiled strategy trades on. -/
theorem exists_repMap (F : Fragment) (K : RationalPolytope F.coords.length) :
    ∃ R : Sentence → ProjectionCompiler.Rep, ∀ (p : Sentence → ℝ)
      (k : Fin F.coords.length),
      repEval F (R (F.coords.get k)) p = K.proj (restrict F p) k := by
  classical
  choose ρ hρ using fun k => exists_rep_repEval F K k
  refine ⟨fun φ => if h : F.coords.idxOf φ < F.coords.length then ρ ⟨_, h⟩ else default,
    fun p k => ?_⟩
  have hidx : F.coords.idxOf (F.coords.get k) = (k : ℕ) := List.get_idxOf F.nodup k
  simp only [hidx, k.isLt, dif_pos, Fin.eta]
  exact hρ k p

/-- The same map, indexed by membership rather than by position: the form the compiled
strategy's correctness hypothesis is stated in. -/
theorem exists_repMap_mem (F : Fragment) (K : RationalPolytope F.coords.length) :
    ∃ R : Sentence → ProjectionCompiler.Rep, ∀ (p : Sentence → ℝ) (φ : Sentence)
      (hφ : φ ∈ F.coords),
      repEval F (R φ) p
        = K.proj (restrict F p) ⟨F.coords.idxOf φ, List.idxOf_lt_length_of_mem hφ⟩ := by
  obtain ⟨R, hR⟩ := exists_repMap F K
  refine ⟨R, fun p φ hφ => ?_⟩
  have hlt : F.coords.idxOf φ < F.coords.length := List.idxOf_lt_length_of_mem hφ
  have hget : F.coords.get ⟨F.coords.idxOf φ, hlt⟩ = φ := List.idxOf_get hlt
  have h := hR p ⟨F.coords.idxOf φ, hlt⟩
  rw [hget] at h
  exact h

/-! ## Nonvacuity

`AGENTS.md` standard 3: the statements above ship with a term inhabiting their hypothesis
package.  That package is a fragment together with a rational polytope of the fragment's
dimension, so the witness is a one-sentence fragment and the unit segment in its single
coordinate. -/

/-- A fragment pricing one sentence. -/
def unitFragment : Fragment where
  coords := [LO.Propositional.Formula.atom 0]
  nodup := List.nodup_singleton _

/-- The bridge is about something: one priced sentence, and the projection onto the unit
segment in its coordinate, represented for the compiler. -/
theorem bridge_nonvacuous :
    ∃ R : Sentence → ProjectionCompiler.Rep, ∀ (p : Sentence → ℝ)
      (k : Fin unitFragment.coords.length),
      repEval unitFragment (R (unitFragment.coords.get k)) p
        = PolyhedralCoverage.unitSegment.proj (restrict unitFragment p) k :=
  exists_repMap unitFragment PolyhedralCoverage.unitSegment

end Workspace.Normativity.Contrib.ProjectionBridge

#print axioms Workspace.Normativity.Contrib.ProjectionBridge.restrict_apply
#print axioms Workspace.Normativity.Contrib.ProjectionBridge.coeff_ofGeom
#print axioms Workspace.Normativity.Contrib.ProjectionBridge.evalR_ofGeom
#print axioms Workspace.Normativity.Contrib.ProjectionBridge.foldr_min_eq_inf'
#print axioms Workspace.Normativity.Contrib.ProjectionBridge.foldr_max_eq_sup'
#print axioms Workspace.Normativity.Contrib.ProjectionBridge.groupEval_groupOf
#print axioms Workspace.Normativity.Contrib.ProjectionBridge.repEval_repOf
#print axioms Workspace.Normativity.Contrib.ProjectionBridge.exists_rep_repEval
#print axioms Workspace.Normativity.Contrib.ProjectionBridge.exists_repMap
#print axioms Workspace.Normativity.Contrib.ProjectionBridge.exists_repMap_mem
#print axioms Workspace.Normativity.Contrib.ProjectionBridge.bridge_nonvacuous
