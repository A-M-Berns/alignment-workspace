import Cleanroom.Bli.BliRvcUi.Ui.Free

/-!
# Audit r2 (adversarial) probe: the schema is load-bearing for `ui_free_nontrivial`

`ui_free_nontrivial` gives `0 < P∞(u) < P∞(inst c) < 1` over `DP ∪ Ax(freeUI)`. An adversary asks
whether the middle inequality could be forced by something other than the schema (Gaifman
coherence, the base). Two checks, over any family-`9`-free base `DP`:

* `base_u_and_not_inst_pos`: over the **base alone** (no schema), every inductor has
  `P∞(u ⋏ ∼inst c) > 0` — the block "`u` true, `inst c` false" is consistent with every base stage.
  So without the schema the violation set keeps positive limiting mass; nothing but the schema can
  kill it.
* `aug_u_and_not_inst_zero`: over `DP ∪ Ax(freeUI)`, `P∞(u ⋏ ∼inst c) = 0` — the schema kills it.

Together: the constraint `ui_limit_of_union` exhibits on `freeUI` is exactly the schema's, and the
witness is N+ for the right reason.
-/

namespace Cleanroom.Bli.BliRvcUi.AuditR2

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Bli.BliRvcUi

variable {DP : DeductiveProcess}
  (hfree : ∀ n, ∀ φ ∈ DP.D n, ∀ p, freshAtomCode 9 p ∉ sentenceAtomCodes φ)
  (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))

include hfree hworld in
/-- Over the base alone, the violation `u ⋏ ∼inst c` keeps positive limiting mass. -/
theorem base_u_and_not_inst_pos {P : History} [IsLogicalInductor P DP] (c : ℕ) :
    0 < limitingBelief P (freeUI.u ⋏ ∼freeUI.inst c) := by
  refine limitingBelief_pos_of_nonDogmatism hworld fun n => ?_
  obtain ⟨v, hv⟩ := hworld n
  refine ⟨famWorld v (fun p => p ≠ Nat.pair 2 c), famWorld_consistentWith hv (hfree n) _, ?_⟩
  rw [PCWorld.holds_and, PCWorld.holds_neg]
  exact ⟨(famWorld_holds_fresh v _ (Nat.pair 1 0)).mpr
      fun h => absurd (Nat.pair_eq_pair.mp h).1 (by norm_num),
    fun h => (famWorld_holds_fresh v _ (Nat.pair 2 c)).mp h rfl⟩

include hworld in
/-- Over the augmented process the schema kills the violation: `P∞(u ⋏ ∼inst c) = 0`. -/
theorem aug_u_and_not_inst_zero {P : History} [IsLogicalInductor P (freeDP DP)]
    (hfree : ∀ n, ∀ φ ∈ DP.D n, ∀ p, freshAtomCode 9 p ∉ sentenceAtomCodes φ) (c : ℕ) :
    limitingBelief P (freeUI.u ⋏ ∼freeUI.inst c) = 0 :=
  limitingBelief_eq_zero_of_theory (freeDP_hworld hfree hworld) fun v hv h => by
    rw [PCWorld.holds_and, PCWorld.holds_neg] at h
    exact h.2 (holds_imp_of_consistentWithTheory_ax
      (PCWorld.consistentWithTheory_union_right hv) c h.1)

end Cleanroom.Bli.BliRvcUi.AuditR2

#print axioms Cleanroom.Bli.BliRvcUi.AuditR2.base_u_and_not_inst_pos
#print axioms Cleanroom.Bli.BliRvcUi.AuditR2.aug_u_and_not_inst_zero
