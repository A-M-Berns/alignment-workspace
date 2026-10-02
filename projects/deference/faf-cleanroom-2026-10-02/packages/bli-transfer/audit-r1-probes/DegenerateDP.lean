import Cleanroom.Bli.BliTransfer.Clamp
import LogicalInduction.Framework.Affine

/-!
# `bli-transfer` · audit round 1 · adversarial lens · probe: `hworld` is load-bearing

**Not imported by the library.** Over a process with an unsatisfiable stage every computable
market is a logical inductor (FAF's `isLogicalInductor_of_stage_unsatisfiable`), the clamp
included. So `clamp_not_isLogicalInductor`'s `hworld` cannot be dropped, and the N+ at
`paperDP 𝗜𝚺₁` (`paperDP_hworld`) is what makes the refutation non-vacuous — trap (v) is real
on the refutation side too.
-/

namespace BliTransferAuditR1

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Bli.BliTransfer

/-- Without consistent worlds the clamp *is* an inductor (given computability): the refutation
needs `hworld`. -/
theorem clamp_isLogicalInductor_of_stage_unsatisfiable (Q : History) (DP : DeductiveProcess)
    (hV : ComputableMarket (clamp Q)) (hDP : ComputableDeductiveProcess DP)
    {N : ℕ} (hN : ∀ v : PCWorld, ¬ v.ConsistentWith (DP.D N)) :
    IsLogicalInductor (clamp Q) DP :=
  isLogicalInductor_of_stage_unsatisfiable (clamp Q) DP hV hDP hN

end BliTransferAuditR1
