import Cleanroom.Bli.BliTransfer.Restricted

/-!
# `bli-transfer` · audit round 1 · adversarial lens · probe: the T2 witness on day `0`

**Not imported by the library.** The `RestrictedEC` witness trades nothing on day `0` (the
mandate asked for a `⊥` trade there; attempt A's F-A4 explains why not). Recorded so the
"genuine day-varying price leaf" claim is read as: one leaf per day from day `1` on.
-/

namespace BliTransferAuditR1

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Bli.BliTransfer

theorem restrictedWitness_day_zero : (restrictedWitness.strat 0).trades = [] := by
  simp [restrictedWitness, restrictedCount]

end BliTransferAuditR1
