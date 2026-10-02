import Cleanroom.Decision.DpLocalOpt.GatedInduction

/-!
# Audit r3 (fidelity) probe: the general theorem on a strongly fair tree with two-node fibers

The only inhabitant of `stronglyFair_strictLocalMax_isOptimal`'s hypothesis package shipped by
the package (`stronglyFair_strictLocalMax_inhabited`) is `twoPoint 2 4 1`, whose `pt` is
injective: every fiber is a singleton (`StronglyFair.of_injective_pt`), so the `LabIso` clause
of `StronglyFair` and the fiber sum in `fiberMass` never bite there. This probe exhibits a
strongly fair tree with two nodes in every fiber — a fair coin between two copies of
`twoPoint 2 4 1` — shows the hypothesis package is inhabited on it, and applies the general
theorem. Not imported by the library.
-/

namespace Cleanroom.Decision.DpLocalOpt.AuditR3

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt

/-- A fair coin between two copies of `twoPoint 2 4 1`: each point sits at two nodes. -/
def fairTwin : Tree TwoW Pt2 (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair ![twoPoint 2 4 1, twoPoint 2 4 1]

/-- `V` on the twin is `V` on one copy. -/
theorem fairTwin_value (C : Proc Pt2 (fun _ => Act2) ℚ) :
    value C fairTwin = value C (twoPoint 2 4 1) := by
  unfold fairTwin
  rw [value_chance, Fin.sum_univ_two]
  simp only [FinDistr.fair, FinDistr.coin, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Two nodes of one copy carrying the same point are the same node, so their subtrees are
labelled-isomorphic. -/
theorem copy_iso (d : Pt2) (q₁ q₂ : (twoPoint 2 4 1).DecNode)
    (h₁ : pt (twoPoint 2 4 1) q₁ = d) (h₂ : pt (twoPoint 2 4 1) q₂ = d) :
    LabIso (subtreeAt (twoPoint 2 4 1) q₁) (subtreeAt (twoPoint 2 4 1) q₂) := by
  have : q₁ = q₂ := twoPoint_pt_injective 2 4 1 (h₁.trans h₂.symm)
  subst this
  exact LabIso.refl _

/-- **The twin is strongly fair**: any two nodes of a fiber sit in (possibly different) copies
at the same node of the copy, so their subtrees are isomorphic. -/
theorem fairTwin_stronglyFair : StronglyFair fairTwin := by
  intro d q hq q' hq'
  rw [mem_fiber] at hq hq'
  obtain ⟨i, q₁⟩ := q
  obtain ⟨j, q₂⟩ := q'
  fin_cases i <;> fin_cases j <;> exact copy_iso d q₁ q₂ hq hq'

/-- The queried points of the twin are those of one copy. -/
theorem fairTwin_queried : queried fairTwin = queried (twoPoint 2 4 1) := by
  unfold fairTwin
  rw [queried_chance]
  ext d
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Fin.exists_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, or_self]

/-- **`(in, x)` is a strict local maximum on the twin** (same `ε` as on one copy). -/
theorem fairTwin_inX_isStrictLocalMax : IsStrictLocalMax inX fairTwin := by
  obtain ⟨ε, hε, h⟩ := twoPoint_inX_isStrictLocalMax
  refine ⟨ε, hε, fun C' hne hnear => ?_⟩
  rw [fairTwin_value, fairTwin_value]
  rw [fairTwin_queried] at hne
  exact h C' hne hnear

/-- The two `p1`-nodes of the twin. -/
def n0 : fairTwin.DecNode := ⟨0, none⟩
def n1 : fairTwin.DecNode := ⟨1, none⟩

/-- **The `p1`-fiber of the twin has two distinct nodes**: strong fairness is not vacuous here. -/
theorem fairTwin_fiber_two_nodes :
    n0 ∈ fiber fairTwin .p1 ∧ n1 ∈ fiber fairTwin .p1 ∧ n0 ≠ n1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_fiber]; rfl
  · rw [mem_fiber]; rfl
  · intro h
    exact absurd (congrArg Sigma.fst h) (by decide)

/-- **The general theorem applied on a tree with two-node fibers**: the hypothesis package is
inhabited, the conclusion holds, and `V` is not constant. -/
theorem fairTwin_package :
    StronglyFair fairTwin ∧ IsStrictLocalMax inX fairTwin ∧ IsOptimal inX fairTwin ∧
    value inX fairTwin = 4 ∧ value outY fairTwin = 2 :=
  ⟨fairTwin_stronglyFair, fairTwin_inX_isStrictLocalMax,
    stronglyFair_strictLocalMax_isOptimal fairTwin fairTwin_stronglyFair inX
      fairTwin_inX_isStrictLocalMax,
    by rw [fairTwin_value, twoPoint_value]; norm_num,
    by rw [fairTwin_value, twoPoint_value]; norm_num⟩

/-- On the twin the `p2`-fiber mass under `(in, x)` is a genuine two-node sum: `½ · 1 + ½ · 1`. -/
theorem fairTwin_fiberMass_p2 : fiberMass inX fairTwin .p2 = 1 := by
  unfold fairTwin
  rw [fiberMass_chance, Fin.sum_univ_two]
  simp only [FinDistr.fair, FinDistr.coin, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h : fiberMass inX (twoPoint 2 4 1) .p2 = 1 := by
    unfold twoPoint
    rw [fiberMass_decision]
    simp only [Act2.sum_univ, fiberMass_leaf, fiberMass_decision, inX, proc2_p1, proc2_p2,
      FinDistr.act2_a, FinDistr.act2_b, if_neg (show ¬ (Pt2.p1 = Pt2.p2) by decide)]
    norm_num
  rw [h]; norm_num

end Cleanroom.Decision.DpLocalOpt.AuditR3
