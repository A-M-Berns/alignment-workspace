import Cleanroom.Bli.BliRvcUi.Ui.Free

/-!
# Audit r2 (adversarial) probe: what the sibling adds is uniformity in `m`, not positivity

`secondLimit_fails_free` (the N+ for the sibling mechanism) shows, over
`DP ∪ Ax(freeUI) ∪ Ax(freeUI')`, `∃ ε > 0, ∀ m, ε ≤ P∞(∼u ⋏ ⋀_{i≤m} inst i)`. This probe checks
what is already true **without** the sibling, over `DP ∪ Ax(freeUI)` alone: for every `m`,
`0 < P∞(∼u ⋏ ⋀_{i≤m} inst i)` (the block "`u` false, everything else true" is consistent with every
stage). So the sibling's contribution is exactly the *uniform* lower bound — the pointwise
positivity is plain non-dogmatism. The package's docstrings say "the bound" without separating the
two; this is a presentation point, not a defect.
-/

namespace Cleanroom.Bli.BliRvcUi.AuditR2

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Bli.BliRvcUi

variable {DP : DeductiveProcess}
  (hfree : ∀ n, ∀ φ ∈ DP.D n, ∀ p, freshAtomCode 9 p ∉ sentenceAtomCodes φ)
  (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))

include hfree hworld in
/-- Without the sibling, each `P∞(∼u ⋏ ⋀_{i≤m} inst i)` is already positive (non-dogmatism on the
block "`u` false, everything else true"); no uniform bound is claimed. -/
theorem noSibling_pointwise_pos {P : History} [IsLogicalInductor P (freeDP DP)] (m : ℕ) :
    0 < limitingBelief P (∼freeUI.u ⋏ instConj freeUI.inst m) := by
  refine limitingBelief_pos_of_nonDogmatism (freeDP_hworld hfree hworld) fun n => ?_
  obtain ⟨v, hv⟩ := hworld n
  refine ⟨famWorld v (fun p => p ≠ Nat.pair 1 0),
    famWorld_consistentWith_free hfree hv _ (fun h => (h rfl).elim), ?_⟩
  rw [PCWorld.holds_and, PCWorld.holds_neg, holds_instConj]
  refine ⟨fun h => (famWorld_holds_fresh v _ (Nat.pair 1 0)).mp h rfl, fun i _ => ?_⟩
  exact (famWorld_holds_fresh v _ (Nat.pair 2 i)).mpr
    fun h => absurd (Nat.pair_eq_pair.mp h).1 (by norm_num)

end Cleanroom.Bli.BliRvcUi.AuditR2

#print axioms Cleanroom.Bli.BliRvcUi.AuditR2.noSibling_pointwise_pos
