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

end Workspace.Normativity.Contrib.ProjectionPrimrec

#print axioms Workspace.Normativity.Contrib.ProjectionPrimrec.efMin_primrec
#print axioms Workspace.Normativity.Contrib.ProjectionPrimrec.sumFeatures_primrec
#print axioms Workspace.Normativity.Contrib.ProjectionPrimrec.tradeListAbsBound_primrec
#print axioms Workspace.Normativity.Contrib.ProjectionPrimrec.calibratedIntensity_primrec
