/-
# Primitive recursion for the compiled projection trader

`EnforcedCompiler` discharges the modified market's computability from one hypothesis:
that the enforcer's trade map is primitive recursive in the date and the ordinary
aggregate's trade list.  This file supplies the ingredients for the projection enforcer,
against the public interface the pinned dependency exports.

Everything here is plumbing — no mathematics — but it is the plumbing that decides whether
"the enforcer is given as effective data" is a fact or a hypothesis.

Names are provisional (`AGENTS.md` standard 6).
-/

import LogicalInduction.Construction.LIACompiler
import Workspace.Normativity.Contrib.ProjectionCalibrated

namespace Workspace.Normativity.Contrib.ProjectionPrimrec

open LogicalInduction
open Workspace.Normativity.Contrib.ProjectionCalibrated

/-! ## Derived expressible-feature constructors -/

lemma efNeg_primrec : Primrec EF.neg := by
  have : Primrec fun e : EF => EF.mul (EF.const (-1)) e :=
    efMul_primrec.comp (Primrec.const (EF.const (-1))) Primrec.id
  exact this.of_eq fun e => rfl

lemma efMin_primrec : Primrec₂ EF.min := by
  have h : Primrec₂ fun a b : EF => EF.neg (EF.max (EF.neg a) (EF.neg b)) :=
    (efNeg_primrec.comp₂
      (efMax_primrec.comp₂ (efNeg_primrec.comp₂ Primrec₂.left)
        (efNeg_primrec.comp₂ Primrec₂.right)))
  exact h.of_eq fun a b => rfl

lemma sumFeatures_primrec : Primrec ROIBudget.sumFeatures := by
  have hstep : Primrec₂ fun (_ : List EF) (p : EF × EF) => EF.add p.1 p.2 :=
    efAdd_primrec.comp₂ (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  have := Primrec.list_foldr Primrec.id (Primrec.const (EF.const 0)) hstep
  exact this.of_eq fun l => rfl

/-! ## Rational list sums -/

lemma ratSum_primrec : Primrec fun l : List ℚ => l.sum := by
  have hstep : Primrec₂ fun (_ : List ℚ) (p : ℚ × ℚ) => p.1 + p.2 :=
    ratAdd_prim.comp₂ (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  have := Primrec.list_foldr Primrec.id (Primrec.const (0 : ℚ)) hstep
  exact this.of_eq fun l => rfl

/-! ## The syntactic bound and the calibrated intensity -/

lemma tradeListAbsBound_primrec : Primrec Strategy.tradeListAbsBound := by
  have hmap : Primrec fun l : List (EF × Sentence) => l.map fun p => p.1.absBound :=
    Primrec.list_map Primrec.id
      (efAbsBound_primrec.comp₂ (Primrec.fst.comp₂ Primrec₂.right))
  exact (ratSum_primrec.comp hmap).of_eq fun l => rfl

lemma resistance_primrec : Primrec₂ resistance := by
  have : Primrec₂ fun (n : ℕ) (A : ℚ) => marketMakerError n + A :=
    ratAdd_prim.comp₂ (marketMakerError_primrec.comp₂ Primrec₂.left) Primrec₂.right
  exact this.of_eq fun n A => rfl

lemma calibratedIntensity_primrec :
    Primrec fun p : (ℕ × ℚ) × ℚ => calibratedIntensity p.1.1 p.1.2 p.2 := by
  have hres : Primrec fun p : (ℕ × ℚ) × ℚ => resistance p.1.1 p.1.2 :=
    resistance_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  have hsq : Primrec fun p : (ℕ × ℚ) × ℚ => p.2 ^ 2 := by
    have : Primrec fun p : (ℕ × ℚ) × ℚ => p.2 * p.2 :=
      ratMul_prim.comp Primrec.snd Primrec.snd
    exact this.of_eq fun p => by ring
  exact (ratDiv_prim.comp hres hsq).of_eq fun p => rfl

/-! ## The compiled expressible features

The compiler's constructions are stated over a `Fragment`, which bundles a `Nodup` proof
and so is awkward to encode.  They only ever read the coordinate list, so the versions
below take that list directly; each agrees with the compiler's by `rfl`. -/

open Workspace.Normativity.Contrib.ProjectionCompiler

/-- `affineEF`, as a function of the coordinate list alone. -/
def affineEFof (coords : List Sentence) (n : ℕ) (a : AffineForm) : EF :=
  ROIBudget.sumFeatures (EF.const a.2 ::
    coords.map fun φ => EF.mul (EF.const (a.1.getD (coords.idxOf φ) 0)) (EF.price φ n))

lemma affineEFof_eq (F : Fragment) (n : ℕ) (a : AffineForm) :
    affineEFof F.coords n a = affineEF F n a := rfl

lemma affineEFof_primrec :
    Primrec fun p : (List Sentence × ℕ) × AffineForm => affineEFof p.1.1 p.1.2 p.2 := by
  let X := (List Sentence × ℕ) × AffineForm
  have hcoords : Primrec fun p : X => p.1.1 := Primrec.fst.comp Primrec.fst
  have hn : Primrec fun p : X => p.1.2 := Primrec.snd.comp Primrec.fst
  have hcoeffs : Primrec fun p : X => p.2.1 := Primrec.fst.comp Primrec.snd
  have hconst : Primrec fun p : X => EF.const p.2.2 :=
    efConst_primrec.comp (Primrec.snd.comp Primrec.snd)
  have hidx : Primrec₂ fun (p : X) (φ : Sentence) => p.1.1.idxOf φ :=
    Primrec.list_idxOf.comp₂ Primrec₂.right (hcoords.comp₂ Primrec₂.left)
  have hget : Primrec₂ fun (p : X) (φ : Sentence) => p.2.1.getD (p.1.1.idxOf φ) 0 :=
    (Primrec.list_getD (0 : ℚ)).comp₂ (hcoeffs.comp₂ Primrec₂.left) hidx
  have hbody : Primrec₂ fun (p : X) (φ : Sentence) =>
      EF.mul (EF.const (p.2.1.getD (p.1.1.idxOf φ) 0)) (EF.price φ p.1.2) :=
    efMul_primrec.comp₂ (efConst_primrec.comp₂ hget)
      (efPrice_primrec.comp₂ Primrec₂.right (hn.comp₂ Primrec₂.left))
  exact (sumFeatures_primrec.comp
    (Primrec.list_cons.comp hconst (Primrec.list_map hcoords hbody))).of_eq fun p => rfl

/-- `groupEF`, as a function of the coordinate list alone. -/
def groupEFof (coords : List Sentence) (n : ℕ) (g : Group) : EF :=
  (g.2.map (affineEFof coords n)).foldr EF.min (affineEFof coords n g.1)

lemma groupEFof_eq (F : Fragment) (n : ℕ) (g : Group) :
    groupEFof F.coords n g = groupEF F n g := rfl

lemma groupEFof_primrec :
    Primrec fun p : (List Sentence × ℕ) × Group => groupEFof p.1.1 p.1.2 p.2 := by
  let Y := (List Sentence × ℕ) × Group
  have hctx : Primrec fun q : Y => q.1 := Primrec.fst
  have hbase : Primrec fun q : Y => affineEFof q.1.1 q.1.2 q.2.1 :=
    affineEFof_primrec.comp (hctx.pair (Primrec.fst.comp Primrec.snd))
  have hlist : Primrec fun q : Y => q.2.2 := Primrec.snd.comp Primrec.snd
  have hmapbody : Primrec₂ fun (q : Y) (a : AffineForm) => affineEFof q.1.1 q.1.2 a := by
    have h : Primrec fun z : Y × AffineForm => affineEFof z.1.1.1 z.1.1.2 z.2 :=
      affineEFof_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
    exact h.to₂
  have hmap : Primrec fun q : Y => q.2.2.map (affineEFof q.1.1 q.1.2) :=
    Primrec.list_map hlist hmapbody
  have hstep : Primrec₂ fun (_ : Y) (pr : EF × EF) => EF.min pr.1 pr.2 :=
    efMin_primrec.comp₂ (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr hmap hbase hstep).of_eq fun q => rfl

/-- `repEF`, as a function of the coordinate list alone. -/
def repEFof (coords : List Sentence) (n : ℕ) (r : Rep) : EF :=
  (r.2.map (groupEFof coords n)).foldr EF.max (groupEFof coords n r.1)

lemma repEFof_eq (F : Fragment) (n : ℕ) (r : Rep) :
    repEFof F.coords n r = repEF F n r := rfl

lemma repEFof_primrec :
    Primrec fun p : (List Sentence × ℕ) × Rep => repEFof p.1.1 p.1.2 p.2 := by
  let Z := (List Sentence × ℕ) × Rep
  have hctx : Primrec fun q : Z => q.1 := Primrec.fst
  have hbase : Primrec fun q : Z => groupEFof q.1.1 q.1.2 q.2.1 :=
    groupEFof_primrec.comp (hctx.pair (Primrec.fst.comp Primrec.snd))
  have hlist : Primrec fun q : Z => q.2.2 := Primrec.snd.comp Primrec.snd
  have hmapbody : Primrec₂ fun (q : Z) (g : Group) => groupEFof q.1.1 q.1.2 g := by
    have h : Primrec fun z : Z × Group => groupEFof z.1.1.1 z.1.1.2 z.2 :=
      groupEFof_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
    exact h.to₂
  have hmap : Primrec fun q : Z => q.2.2.map (groupEFof q.1.1 q.1.2) :=
    Primrec.list_map hlist hmapbody
  have hstep : Primrec₂ fun (_ : Z) (pr : EF × EF) => EF.max pr.1 pr.2 :=
    efMax_primrec.comp₂ (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr hmap hbase hstep).of_eq fun q => rfl

/-- `coefEF`, as a function of the coordinate list alone. -/
def coefEFof (coords : List Sentence) (n : ℕ) (lam : ℚ) (r : Rep) (φ : Sentence) : EF :=
  EF.mul (EF.const lam) (EF.add (repEFof coords n r) (EF.neg (EF.price φ n)))

lemma coefEFof_eq (F : Fragment) (n : ℕ) (lam : ℚ) (r : Rep) (φ : Sentence) :
    coefEFof F.coords n lam r φ = coefEF F n lam r φ := rfl

lemma coefEFof_primrec :
    Primrec fun p : ((List Sentence × ℕ) × ℚ) × (Rep × Sentence) =>
      coefEFof p.1.1.1 p.1.1.2 p.1.2 p.2.1 p.2.2 := by
  let W := ((List Sentence × ℕ) × ℚ) × (Rep × Sentence)
  have hctx : Primrec fun q : W => q.1.1 := Primrec.fst.comp Primrec.fst
  have hlam : Primrec fun q : W => EF.const q.1.2 :=
    efConst_primrec.comp (Primrec.snd.comp Primrec.fst)
  have hrep : Primrec fun q : W => repEFof q.1.1.1 q.1.1.2 q.2.1 :=
    repEFof_primrec.comp (hctx.pair (Primrec.fst.comp Primrec.snd))
  have hprice : Primrec fun q : W => EF.neg (EF.price q.2.2 q.1.1.2) :=
    efNeg_primrec.comp (efPrice_primrec.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.snd.comp hctx))
  exact (efMul_primrec.comp hlam (efAdd_primrec.comp hrep hprice)).of_eq fun q => rfl

end Workspace.Normativity.Contrib.ProjectionPrimrec

#print axioms Workspace.Normativity.Contrib.ProjectionPrimrec.efMin_primrec
#print axioms Workspace.Normativity.Contrib.ProjectionPrimrec.sumFeatures_primrec
#print axioms Workspace.Normativity.Contrib.ProjectionPrimrec.tradeListAbsBound_primrec
#print axioms Workspace.Normativity.Contrib.ProjectionPrimrec.calibratedIntensity_primrec
#print axioms Workspace.Normativity.Contrib.ProjectionPrimrec.affineEFof_primrec
#print axioms Workspace.Normativity.Contrib.ProjectionPrimrec.groupEFof_primrec
#print axioms Workspace.Normativity.Contrib.ProjectionPrimrec.repEFof_primrec
#print axioms Workspace.Normativity.Contrib.ProjectionPrimrec.coefEFof_primrec
