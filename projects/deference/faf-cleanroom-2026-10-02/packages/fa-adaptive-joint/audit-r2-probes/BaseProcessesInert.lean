import Cleanroom.Fa.FaAdaptiveJoint.JointClearing

/-!
# `fa-adaptive-joint` · audit r2 (fidelity) · probe: the base processes are still inert in the carrier

Evidence for `fa-adaptive-joint-audit-r2-fidelity.md`. **Not imported by the library.**

Repair round 1 tied the carrier's families to the two halves (`LUV.tagH`/`tagA`), which is what
audit r1 B2 asked for, and that is the part that matters: the sides `sideH M`, `sideA M` are now
genuinely distinct projections. This probe records what the repair did *not* change: the base
processes `DPH`, `DPA` enter the carrier only through `merged_sub`, which no headline uses, so a
pair over any `DPH, DPA` forgets to a pair over the empty processes with the same market, process
and (tagged) families, and `v3Theorems_of_jointClearing` on the forgotten pair is the identical
conclusion. Non-blocking: the ledger should say that `DPH`/`DPA` enter the headline only through
the OPEN existence row's hypotheses (`hH`, `hA`, `hval`), not through the statement.
-/

namespace Cleanroom.Fa.FaAdaptiveJoint.AuditR2

open LogicalInduction Cleanroom.Fa.FaForcingTrader Cleanroom.Fa.FaTheoremA
  Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Filter Topology

/-- The empty deductive process. -/
def emptyProcess : DeductiveProcess where
  D _ := ∅
  mono _ := Finset.Subset.refl _

theorem mergedProcess_empty_D (n : ℕ) : (mergedProcess emptyProcess emptyProcess).D n = ∅ := by
  simp [mergedProcess, mergedStage, emptyProcess]

/-- The base processes are inert in the repaired carrier too. -/
def jointClearingPair_forget {DPH DPA : DeductiveProcess} {f : DeferralFunction}
    (P : JointClearingPair DPH DPA f) : JointClearingPair emptyProcess emptyProcess f :=
  { P with merged_sub := fun n => by rw [mergedProcess_empty_D]; exact Finset.empty_subset _ }

/-- The headline on the forgotten pair is the identical conclusion (same `M`, `X`, `Y`). -/
theorem forget_same_conclusion {DPH DPA : DeductiveProcess} {f : DeferralFunction}
    (P : JointClearingPair DPH DPA f) (t ε : ℚ) {δ : ℚ} (hδ : 0 < δ) (hε : 0 < ε)
    (hbridge : AdaptiveBridgeHolds P.M f (fun n => LUV.tagH (P.X n))) :
    Tendsto (viol (fun n => (P.X n).expect P.H n) (quoteSeq P.Y P.A) t ε δ) atTop (𝓝 0) :=
  v3Theorems_of_jointClearing (jointClearingPair_forget P) t ε hδ hε hbridge

end Cleanroom.Fa.FaAdaptiveJoint.AuditR2
