import Cleanroom.Corrigibility.CorrValueChange.Savage
import Mathlib.Tactic.NormNum

/-!
Audit r4 (adversarial) probe for `corr-value-change`, T13(d) `edt_eq_savage` / findings F15.

`edt_eq_savage` says the Savage model of a product model agrees with the evidential two-step model
on `p`, `v`, `w` unconditionally and on `v_K` under the uninformative-choice assumption (F15: "exactly
when"). This probe checks that the assumption is load-bearing for `v_K`: a product model whose
step-1 choice is informative about the facts (keep worlds all have `f = true`, change worlds all
`f = false`) has evidential `v_K = 1` and Savage `v_K = 0`. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open Finset

noncomputable section

/-- One fact bit, one outcome, one act; the keep configuration carries `f = true`, the change
configuration `f = false`; `U(f, K, ·) = [f = true]`, `U(f, C, ·) = 0`. -/
def infoPM : ProductModel Bool Unit Unit where
  q := fun f c => match c with
    | none => if f then 1 / 2 else 0
    | some _ => if f then 0 else 1 / 2
  q_nonneg := fun f c => by cases c <;> cases f <;> simp
  q_sum := by simp [Fintype.sum_bool, Fintype.sum_option, Fintype.sum_unique]; norm_num
  σ := fun _ => 1
  σ_pos := fun _ => by norm_num
  σ_sum := by simp
  Uf := fun f c _ => match c with
    | none => if f then 1 else 0
    | some _ => 0
  qK_pos := by simp [Fintype.sum_bool]
  qC_pos := fun _ => by simp [Fintype.sum_bool]

theorem infoPM_not_uninformative : ¬ infoPM.Uninformative := by
  intro h
  have := h true
  simp [infoPM, ProductModel.qK, ProductModel.qCtot, ProductModel.qC, Fintype.sum_bool,
    Fintype.sum_unique] at this

theorem infoPM_vK_edt : infoPM.toTwoStep.vK infoPM.U () = 1 := by
  rw [ProductModel.toTwoStep_vK]
  simp [ProductModel.vKf, infoPM, ProductModel.qK, Fintype.sum_bool]

theorem infoPM_vK_savage : infoPM.toSavage.vK () = 0 := by
  simp [Savage.vK, ProductModel.toSavage, Prob.integral, infoPM, Fintype.sum_prod_type,
    Fintype.sum_bool, Fintype.sum_unique]

/-- **The uninformative-choice assumption is load-bearing in `edt_eq_savage`**: without it the two
`v_K` differ. -/
theorem probe_savage_needs_uninformative :
    ¬ infoPM.Uninformative ∧ infoPM.toSavage.vK () ≠ infoPM.toTwoStep.vK infoPM.U () := by
  refine ⟨infoPM_not_uninformative, ?_⟩
  rw [infoPM_vK_savage, infoPM_vK_edt]; norm_num

end

end Cleanroom.Corrigibility.CorrValueChange
