/-
# Compiling the projector into a trading strategy

A Logical Induction strategy is a finite list of `(expressible feature, sentence)`
pairs.  An expressible feature is built from price features, rational constants,
`+`, `×`, `max` and safe reciprocation — it is **not** allowed to be an arbitrary
optimization subroutine evaluated at the eventual price.  So the projection trader
of `ProjectionForce` is only a legal trader if `p ↦ proj_K(p)` can be written in
that grammar.

It can, and this file does it, at the following boundary.

**What is proved here.** Given, for each priced sentence, a *max-min representation*
— a nonempty finite list of nonempty finite groups of rational affine forms — the
compiled term is a legal `EF` of rank `≤ n`, its real denotation is the max-min
value of the representation, its exact rational denotation is the same computation
in `ℚ`, and the resulting `Strategy n` realizes the projection position in the sense
`ProjectionMarket.Realizes` requires.  Support is exactly the fragment; continuity
is the source's `EF.continuous_denote`.

**What is supplied from outside.** That such a representation *exists* for the
Euclidean projector of a nonempty rational polytope, and is computable from a
rational description of it.  That is two classical facts, cited and not reproved
here:

* the Euclidean projection onto a polyhedron is a continuous piecewise-affine map
  of the point being projected, with polyhedral pieces indexed by the active set and
  rational affine data on each — the solution map of a strictly convex parametric
  quadratic program with the parameter entering linearly (Bemporad, Morari, Dua and
  Pistikopoulos, *The explicit linear quadratic regulator for constrained systems*,
  Automatica 38 (2002) 3–20; see also Rockafellar and Wets, *Variational Analysis*,
  §12.E for polyhedral projection as a piecewise-affine map);
* every continuous piecewise-affine function on a convex polyhedral domain is a
  max of mins of its affine components (Ovchinnikov, *Max-min representation of
  piecewise linear functions*, Beiträge zur Algebra und Geometrie 43 (2002)
  297–302; see also Scholtes, *Introduction to Piecewise Differentiable Equations*,
  Springer 2012, §2.2).

Neither is stated as an axiom.  The theorems below take the representation as
**data** and its correctness as a hypothesis, which is what a compiler that
enumerated the pieces would supply.  `ProjectionCompiler.md` in the round records
the cost: the number of pieces is exponential in the fragment, so the construction
is computable and not efficient.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.ProjectionMarket

namespace Workspace.Normativity.Contrib.ProjectionCompiler

open LogicalInduction
open Workspace.Normativity.Contrib.ProjectionForce
open Workspace.Normativity.Contrib.ProjectionMarket

/-! ## Fragments, as data

The priced fragment is carried as a duplicate-free **list**, not as a `Finset`.
`Finset.toList` is noncomputable, and a compiler whose output is noncomputable is
not a compiler; every definition below is a `def`. -/

/-- A finite priced fragment, as data. -/
structure Fragment where
  /-- The priced sentences, listed once each. -/
  coords : List Sentence
  /-- Each priced sentence is listed once. -/
  nodup : coords.Nodup

/-- The fragment as a `Finset`, for the statements the algebra is phrased over. -/
def Fragment.toFinset (F : Fragment) : Finset Sentence := F.coords.toFinset

lemma Fragment.sum_eq (F : Fragment) (f : Sentence → ℝ) :
    ∑ φ ∈ F.toFinset, f φ = (F.coords.map f).sum :=
  List.sum_toFinset f F.nodup

lemma Fragment.sum_eqQ (F : Fragment) (f : Sentence → ℚ) :
    ∑ φ ∈ F.toFinset, f φ = (F.coords.map f).sum :=
  List.sum_toFinset f F.nodup

/-! ## Rational affine forms on a fragment -/

/-- An affine form on the fragment: the coefficients, positionally aligned with the
fragment's coordinate list, paired with the constant term.  A product of standard types
rather than a structure, so that it and everything built from it are `Primcodable` with no
instances to write — and finite data rather than a function on sentences, which could never
be an input to a primitive-recursive evaluator. -/
abbrev AffineForm : Type := List ℚ × ℚ

/-- The coefficient the form puts on a priced sentence: positional lookup against the
fragment, `0` outside it.  `List.idxOf` and `List.getD` both have primitive-recursive
certificates, which an association lookup does not. -/
def AffineForm.coeff (F : Fragment) (a : AffineForm) (φ : Sentence) : ℚ :=
  a.1.getD (F.coords.idxOf φ) 0

/-- The real value of an affine form at a price vector. -/
def AffineForm.evalR (F : Fragment) (a : AffineForm) (p : Sentence → ℝ) : ℝ :=
  (a.2 : ℝ) + ∑ φ ∈ F.toFinset, (a.coeff F φ : ℝ) * p φ

/-- The exact rational value of an affine form at a rational price vector. -/
def AffineForm.evalQ (F : Fragment) (a : AffineForm) (p : Sentence → ℚ) : ℚ :=
  a.2 + ∑ φ ∈ F.toFinset, a.coeff F φ * p φ

/-- The affine form, as an expressible feature of rank `n`. -/
def affineEF (F : Fragment) (n : ℕ) (a : AffineForm) : EF :=
  ROIBudget.sumFeatures
    (EF.const a.2 :: F.coords.map fun φ => EF.mul (EF.const (a.coeff F φ)) (EF.price φ n))

lemma affineEF_rank_le (F : Fragment) (n : ℕ) (a : AffineForm) :
    (affineEF F n a).rank ≤ n := by
  apply ROIBudget.sumFeatures_rank_le
  intro e he
  rcases List.mem_cons.mp he with rfl | he'
  · simp [EF.rank]
  · simp only [List.mem_map] at he'
    obtain ⟨φ, _, rfl⟩ := he'
    simp [EF.rank]

lemma affineEF_denote (F : Fragment) (n : ℕ) (a : AffineForm) (V : History) :
    (affineEF F n a).denote V = a.evalR F (V n) := by
  rw [affineEF, ROIBudget.sumFeatures_denote, AffineForm.evalR, F.sum_eq]
  simp only [List.map_cons, List.sum_cons, List.map_map]
  congr 1

/-! ## Max-min representations

A representation is a nonempty list of nonempty groups.  The nesting is explicit
rather than defaulted, so no neutral element leaks into the value. -/

/-- A nonempty finite group of affine forms, to be minimised over. -/
abbrev Group : Type := AffineForm × List AffineForm

/-- A nonempty finite list of groups, to be maximised over. -/
abbrev Rep : Type := Group × List Group

/-- The compiled minimum over one group. -/
def groupEF (F : Fragment) (n : ℕ) (g : Group) : EF :=
  (g.2.map (affineEF F n)).foldr EF.min (affineEF F n g.1)

/-- The compiled max of mins. -/
def repEF (F : Fragment) (n : ℕ) (r : Rep) : EF :=
  (r.2.map (groupEF F n)).foldr EF.max (groupEF F n r.1)

/-- The real value of a group. -/
def groupEval (F : Fragment) (g : Group) (p : Sentence → ℝ) : ℝ :=
  (g.2.map fun a => a.evalR F p).foldr min (g.1.evalR F p)

/-- The real value of a representation. -/
def repEval (F : Fragment) (r : Rep) (p : Sentence → ℝ) : ℝ :=
  (r.2.map fun g => groupEval F g p).foldr max (groupEval F r.1 p)

lemma groupEF_rank_le (F : Fragment) (n : ℕ) (g : Group) :
    (groupEF F n g).rank ≤ n := by
  unfold groupEF
  induction g.2 with
  | nil => exact affineEF_rank_le F n g.1
  | cons a as ih =>
      simp only [List.map_cons, List.foldr_cons, EF.rank_min, Nat.max_le]
      exact ⟨affineEF_rank_le F n a, ih⟩

lemma repEF_rank_le (F : Fragment) (n : ℕ) (r : Rep) :
    (repEF F n r).rank ≤ n := by
  unfold repEF
  induction r.2 with
  | nil => exact groupEF_rank_le F n r.1
  | cons g gs ih =>
      simp only [List.map_cons, List.foldr_cons, EF.rank_max, Nat.max_le]
      exact ⟨groupEF_rank_le F n g, ih⟩

lemma groupEF_denote (F : Fragment) (n : ℕ) (g : Group) (V : History) :
    (groupEF F n g).denote V = groupEval F g (V n) := by
  unfold groupEF groupEval
  induction g.2 with
  | nil => exact affineEF_denote F n g.1 V
  | cons a as ih =>
      simp only [List.map_cons, List.foldr_cons]
      rw [EF.denote_min, ih, affineEF_denote]

lemma repEF_denote (F : Fragment) (n : ℕ) (r : Rep) (V : History) :
    (repEF F n r).denote V = repEval F r (V n) := by
  unfold repEF repEval
  induction r.2 with
  | nil => exact groupEF_denote F n r.1 V
  | cons g gs ih =>
      simp only [List.map_cons, List.foldr_cons]
      rw [EF.denote_max, ih, groupEF_denote]

/-! ## The compiled strategy -/

/-- The day-`n` coefficient on `φ`: the intensity times the displacement of the
represented projection from the displayed price. -/
def coefEF (F : Fragment) (n : ℕ) (lam : ℚ) (r : Rep) (φ : Sentence) : EF :=
  EF.mul (EF.const lam) (EF.add (repEF F n r) (EF.neg (EF.price φ n)))

lemma coefEF_rank_le (F : Fragment) (n : ℕ) (lam : ℚ) (r : Rep) (φ : Sentence) :
    (coefEF F n lam r φ).rank ≤ n := by
  simp only [coefEF, EF.neg, EF.rank_mul, EF.rank_add, EF.rank_const, EF.rank_price,
    Nat.zero_max, Nat.max_le]
  exact ⟨repEF_rank_le F n r, le_rfl⟩

lemma coefEF_denote (F : Fragment) (n : ℕ) (lam : ℚ) (r : Rep) (φ : Sentence)
    (V : History) :
    (coefEF F n lam r φ).denote V = (lam : ℝ) * (repEval F r (V n) - V n φ) := by
  simp only [coefEF, EF.denote_mul, EF.denote_add, EF.denote_const, EF.denote_price,
    Pi.mul_apply, Pi.add_apply, EF.denote_neg, repEF_denote]
  ring

/-- **The compiled projection strategy.**  One trade per priced sentence, at the
compiled coefficient.  A `def`, not a `noncomputable def`: given the representations
as data it is finite syntax computed from the fragment, the date and the intensity. -/
def projectionStrategy (F : Fragment) (n : ℕ) (lam : ℚ)
    (R : Sentence → Rep) : Strategy n where
  trades := F.coords.map fun φ => (coefEF F n lam (R φ) φ, φ)
  rank_le := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨φ, _, rfl⟩ := hp
    exact coefEF_rank_le F n lam (R φ) φ

/-- The traded support is exactly the fragment. -/
theorem projectionStrategy_support (F : Fragment) (n : ℕ) (lam : ℚ)
    (R : Sentence → Rep) :
    (projectionStrategy F n lam R).support = F.toFinset := by
  ext φ
  simp only [projectionStrategy, Strategy.support, Fragment.toFinset, Finset.mem_image,
    List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨ψ, hψ, rfl⟩ := hp
    exact hψ
  · intro hφ
    exact ⟨(coefEF F n lam (R φ) φ, φ), ⟨φ, hφ, rfl⟩, rfl⟩

/-- Every compiled coefficient denotes a continuous function of the history, which
is the hypothesis the fixed-point lemma applies Brouwer to. -/
theorem coefEF_continuous (F : Fragment) (n : ℕ) (lam : ℚ) (r : Rep)
    (φ : Sentence) : Continuous (coefEF F n lam r φ).denote :=
  EF.continuous_denote _

/-- **The compiled strategy realizes the projection position.**  The hypothesis is
exactly the correctness of the supplied representations: at the day's prices, the
represented value is the projection's coordinate. -/
theorem projectionStrategy_realizes (F : Fragment) (n : ℕ) (lam : ℚ)
    (R : Sentence → Rep) (V : History) (q : Sentence → ℝ)
    (hR : ∀ φ ∈ F.coords, repEval F (R φ) (V n) = q φ) :
    Realizes F.toFinset (lam : ℝ) q (projectionStrategy F n lam R) V := by
  intro w
  rw [Strategy.value, projectionStrategy]
  simp only [List.map_map]
  unfold ip shares
  rw [F.sum_eq]
  refine congrArg List.sum (List.map_congr_left fun φ hφ => ?_)
  simp only [Function.comp_apply]
  rw [coefEF_denote, hR φ hφ]

/-! ## Exact rational semantics

The market's displayed prices are exactly rational, so the compiled term is
evaluated by `EF.denoteRat` in `ℚ` with no approximation anywhere.  The rational
computation matches the real one term by term. -/

private lemma denoteRat_const (c : ℚ) (V : ℕ → Sentence → ℚ) :
    (EF.const c).denoteRat V = c := rfl

private lemma denoteRat_mul (a b : EF) (V : ℕ → Sentence → ℚ) :
    (a.mul b).denoteRat V = a.denoteRat V * b.denoteRat V := rfl

private lemma denoteRat_max (a b : EF) (V : ℕ → Sentence → ℚ) :
    (a.max b).denoteRat V = Max.max (a.denoteRat V) (b.denoteRat V) := rfl

private lemma denoteRat_min (a b : EF) (V : ℕ → Sentence → ℚ) :
    (EF.min a b).denoteRat V = Min.min (a.denoteRat V) (b.denoteRat V) := by
  simp only [EF.min, EF.neg, denoteRat_mul, denoteRat_max, denoteRat_const]
  rcases le_total (a.denoteRat V) (b.denoteRat V) with h | h
  · rw [min_eq_left h,
      max_eq_left (by linarith : (-1 : ℚ) * b.denoteRat V ≤ -1 * a.denoteRat V)]
    ring
  · rw [min_eq_right h,
      max_eq_right (by linarith : (-1 : ℚ) * a.denoteRat V ≤ -1 * b.denoteRat V)]
    ring

private lemma sumFeatures_denoteRat (es : List EF) (V : ℕ → Sentence → ℚ) :
    (ROIBudget.sumFeatures es).denoteRat V = (es.map fun e => e.denoteRat V).sum := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      change e.denoteRat V + (ROIBudget.sumFeatures es).denoteRat V =
        e.denoteRat V + (es.map fun e => e.denoteRat V).sum
      rw [ih]

lemma affineEF_denoteRat (F : Fragment) (n : ℕ) (a : AffineForm)
    (V : ℕ → Sentence → ℚ) :
    (affineEF F n a).denoteRat V = a.evalQ F (V n) := by
  rw [affineEF, sumFeatures_denoteRat, AffineForm.evalQ, F.sum_eqQ]
  simp only [List.map_cons, List.sum_cons, List.map_map]
  congr 1

/-- The exact rational value of a group. -/
def groupEvalQ (F : Fragment) (g : Group) (p : Sentence → ℚ) : ℚ :=
  (g.2.map fun a => a.evalQ F p).foldr min (g.1.evalQ F p)

/-- The exact rational value of a representation. -/
def repEvalQ (F : Fragment) (r : Rep) (p : Sentence → ℚ) : ℚ :=
  (r.2.map fun g => groupEvalQ F g p).foldr max (groupEvalQ F r.1 p)

lemma groupEF_denoteRat (F : Fragment) (n : ℕ) (g : Group)
    (V : ℕ → Sentence → ℚ) :
    (groupEF F n g).denoteRat V = groupEvalQ F g (V n) := by
  unfold groupEF groupEvalQ
  induction g.2 with
  | nil => exact affineEF_denoteRat F n g.1 V
  | cons a as ih =>
      simp only [List.map_cons, List.foldr_cons]
      rw [denoteRat_min, ih, affineEF_denoteRat]

/-- **Exactness.**  At rational market prices the compiled representation evaluates
in `ℚ`, with no rounding and no approximation: the same max-min computation the real
semantics performs. -/
theorem repEF_denoteRat (F : Fragment) (n : ℕ) (r : Rep)
    (V : ℕ → Sentence → ℚ) :
    (repEF F n r).denoteRat V = repEvalQ F r (V n) := by
  unfold repEF repEvalQ
  induction r.2 with
  | nil => exact groupEF_denoteRat F n r.1 V
  | cons g gs ih =>
      simp only [List.map_cons, List.foldr_cons]
      rw [denoteRat_max, ih, groupEF_denoteRat]

end Workspace.Normativity.Contrib.ProjectionCompiler

#print axioms Workspace.Normativity.Contrib.ProjectionCompiler.affineEF_rank_le
#print axioms Workspace.Normativity.Contrib.ProjectionCompiler.affineEF_denote
#print axioms Workspace.Normativity.Contrib.ProjectionCompiler.repEF_rank_le
#print axioms Workspace.Normativity.Contrib.ProjectionCompiler.repEF_denote
#print axioms Workspace.Normativity.Contrib.ProjectionCompiler.projectionStrategy
#print axioms Workspace.Normativity.Contrib.ProjectionCompiler.projectionStrategy_support
#print axioms Workspace.Normativity.Contrib.ProjectionCompiler.coefEF_continuous
#print axioms Workspace.Normativity.Contrib.ProjectionCompiler.projectionStrategy_realizes
#print axioms Workspace.Normativity.Contrib.ProjectionCompiler.repEF_denoteRat
