import Cleanroom.Corrigibility.CorrChannelVoi.Coupling

/-!
# `corr-channel-voi` · audit r3 (adversarial) probe: T14 Case B is an arithmetic stub

Not imported by the library.

`honest_advisory_dominates` (ledger T14, Kind `L`) is `v + m − δ ≤ v + max(m, Q)` for `δ ≥ 0`
over Holtman's transcribed displays. The first theorem proves the bare inequality with no package
definition in sight (`m − δ ≤ m ≤ max(m, Q)`); the second shows the package's theorem is that
inequality under two definitional unfoldings. Under [[AUDIT]] §0.2 this is a *Stub* (`T`): the
unmodeled argument is Holtman's derivation of the two values, which the (c) disclosure names.
-/

namespace Cleanroom.Corrigibility.CorrChannelVoi.AuditR3Adversarial

open Cleanroom.Corrigibility.CorrChannelVoi

theorem advisory_bare (v m Q δ : ℝ) (hδ : 0 ≤ δ) : v + m - δ ≤ v + max m Q := by
  linarith [le_max_left m Q]

theorem honest_advisory_dominates_is_bare (v m Q δ : ℝ) (hδ : 0 ≤ δ) :
    deceptiveAdvisory v m δ ≤ honestAdvisory v m Q := by
  unfold deceptiveAdvisory honestAdvisory
  exact advisory_bare v m Q δ hδ

end Cleanroom.Corrigibility.CorrChannelVoi.AuditR3Adversarial
