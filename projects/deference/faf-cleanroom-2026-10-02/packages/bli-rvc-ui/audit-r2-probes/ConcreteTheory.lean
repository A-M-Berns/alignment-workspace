import Cleanroom.Bli.BliRvcUi.Ui.Free

/-!
# Audit r2 (adversarial) probe: the N+ packages are inhabited at a concrete theory

`ui_free_paper_lia T` and `secondLimit_fails_free_paper_lia T` quantify over
`[T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Consistent T]`. If no concrete `T` carried those instances, the "for every
inductor" statements would range over an empty class and the N+ grades would be hollow. This
probe instantiates both at `T := 𝗜𝚺₁` and FAF's own inductor `liaHistory`: the instance package
resolves, so the witnesses are inhabited at a real theory.
-/

namespace Cleanroom.Bli.BliRvcUi.AuditR2

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Bli.BliRvcUi

/-- T3.3's N+ at `𝗜𝚺₁`, FAF's inductor, instance `0`: both sides interior, strict. -/
theorem ui_free_isigma1 :
    0 < limitingBelief (liaHistory (paperFree 𝗜𝚺₁)) freeUI.u ∧
    limitingBelief (liaHistory (paperFree 𝗜𝚺₁)) freeUI.u <
      limitingBelief (liaHistory (paperFree 𝗜𝚺₁)) (freeUI.inst 0) ∧
    limitingBelief (liaHistory (paperFree 𝗜𝚺₁)) (freeUI.inst 0) < 1 :=
  ui_free_paper_lia 𝗜𝚺₁ 0

/-- T3.7 (b)'s sibling N+ at `𝗜𝚺₁`, FAF's inductor. -/
theorem secondLimit_free_isigma1 :
    ∃ ε : ℝ, 0 < ε ∧ ∀ m, ε ≤ limitingBelief (liaHistory (paperFree2 𝗜𝚺₁))
      (∼freeUI.u ⋏ instConj freeUI.inst m) :=
  secondLimit_fails_free_paper_lia 𝗜𝚺₁

/-- … with the instances undecided there (`P∞(inst c) < 1`). -/
theorem free2_inst_isigma1 (c : ℕ) :
    limitingBelief (liaHistory (paperFree2 𝗜𝚺₁)) (freeUI.inst c) < 1 :=
  haveI := LIA_is_logical_inductor (paperFree2 𝗜𝚺₁) (paperFree2_computable 𝗜𝚺₁)
  free2_inst_lt_one_paper 𝗜𝚺₁ c

end Cleanroom.Bli.BliRvcUi.AuditR2

#print axioms Cleanroom.Bli.BliRvcUi.AuditR2.ui_free_isigma1
#print axioms Cleanroom.Bli.BliRvcUi.AuditR2.secondLimit_free_isigma1
#print axioms Cleanroom.Bli.BliRvcUi.AuditR2.free2_inst_isigma1
