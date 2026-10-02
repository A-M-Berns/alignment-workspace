import Cleanroom.Decision.DpFaithfulUdt.KfoldAffine

/-!
# Audit r2 (adversarial) probe: the `convexB 2` instance the ledger cites without a declaration

The ledger's witness cell for `kfold2_norm_faithful_both_iff_affine` lists "`convexB 2` (refuse
only, by the mirror)" — no declaration in the package states it. This probe instantiates the two
proved characterizations at `convexB 2 = (0, 0, 1)` (normalized, non-affine): refuse-faithful sets
exist for every full-support self-model (the first-draw set, `b_1 = b_0 = 0`), and no pay-faithful
set exists for every self-model (already none at `q' = ½`). So the convex coupling inhabits the
"refuse only" cell non-degenerately, and the biconditional's hypothesis package (`b_0 = 0`,
`b_2 = 1`, `x, y > 0`) is exercised by a third normalized data point beside `linearB 2` (both)
and `concaveB` (pay only). Not imported by the library.
-/

namespace Cleanroom.Decision.DpFaithfulUdt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt

theorem convexB2_vals : convexB 2 0 = 0 ∧ convexB 2 1 = 0 ∧ convexB 2 2 = 1 := by
  simp [convexB]

/-- `convexB 2` is normalized and refuse-faithful sets exist for every full-support self-model. -/
theorem convex2_refuse_faithful_all (x y : ℚ) (hx : 0 < x) (hy : 0 < y) :
    ∀ q' (h0 : 0 < q') (h1 : q' < 1),
      ∃ E : Finset (kfold 2 x y (convexB 2) (convexB_bounds 2)).Leaves,
        LeafLawFaithfulWrt (kfold 2 x y (convexB 2) (convexB_bounds 2))
          (kfLab x y (convexB 2) (convexB_bounds 2)) (procQ q' h0.le h1.le) () .b E :=
  (kfold2_norm_refuse_faithful_iff x y (convexB 2) (convexB_bounds 2) hx hy convexB2_vals.1
    convexB2_vals.2.2).mpr (Or.inl convexB2_vals.2.1)

/-- On `convexB 2` no pay-faithful set exists for every self-model (`b_1 = 0 ∉ {½, 1}`). -/
theorem convex2_no_pay_faithful_all (x y : ℚ) (hx : 0 < x) (hy : 0 < y) :
    ¬ ∀ q' (h0 : 0 < q') (h1 : q' < 1),
      ∃ E : Finset (kfold 2 x y (convexB 2) (convexB_bounds 2)).Leaves,
        LeafLawFaithfulWrt (kfold 2 x y (convexB 2) (convexB_bounds 2))
          (kfLab x y (convexB 2) (convexB_bounds 2)) (procQ q' h0.le h1.le) () .a E := by
  intro h
  have := (kfold2_norm_pay_faithful_iff x y (convexB 2) (convexB_bounds 2) hx hy convexB2_vals.1
    convexB2_vals.2.2).mp h
  rw [convexB2_vals.2.1] at this
  norm_num at this

/-- `convexB 2` is not affine on `0..2`, so by `kfold2_norm_faithful_both_iff_affine` faithful sets
for *both* acts do not exist for every self-model — consistent with the two rows above. -/
theorem convex2_not_both (x y : ℚ) (hx : 0 < x) (hy : 0 < y) :
    ¬ ∀ q' (h0 : 0 < q') (h1 : q' < 1), ∀ a : Act2,
      ∃ E : Finset (kfold 2 x y (convexB 2) (convexB_bounds 2)).Leaves,
        LeafLawFaithfulWrt (kfold 2 x y (convexB 2) (convexB_bounds 2))
          (kfLabK 2 x y (convexB 2) (convexB_bounds 2)) (procQ q' h0.le h1.le) () a E := by
  intro h
  have := (kfold2_norm_faithful_both_iff_affine x y (convexB 2) (convexB_bounds 2) hx hy
    convexB2_vals.1 convexB2_vals.2.2).mp h
  obtain ⟨α, β, hab⟩ := this
  have e0 := hab 0 (by norm_num)
  have e1 := hab 1 (by norm_num)
  have e2 := hab 2 (by norm_num)
  simp [convexB] at e0 e1 e2
  linarith

end Cleanroom.Decision.DpFaithfulUdt

#print axioms Cleanroom.Decision.DpFaithfulUdt.convex2_refuse_faithful_all
#print axioms Cleanroom.Decision.DpFaithfulUdt.convex2_no_pay_faithful_all
#print axioms Cleanroom.Decision.DpFaithfulUdt.convex2_not_both
