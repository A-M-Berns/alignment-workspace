import Cleanroom.Deference.DefTrackingPin.Witnesses

/-!
Audit round 3 (fidelity) probe for `def-tracking-pin`. Not imported by the library.

The ledger row for `deferred_diagonal_subsequence` (T6 stretch, proved at repair round 2) claims
N+ by argument — "the paper pair with `φ` any computable enumeration inhabits every hypothesis
… no separate instance shipped". [[STANDARDS]] §3 asks for a shipped witness. This file checks
the claim: every hypothesis of `deferred_diagonal_subsequence` discharged from FAF's facts at the
paper pair with the pairing enumeration `quoted _ n := witnessSentence n.unpair.1`.
-/

namespace Cleanroom.Deference.DefTrackingPin

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane
open Filter Topology

/-- The pairing-enumeration quoted table (day `n` quotes `witnessSentence (n.unpair.1)`, every
item) is computable. -/
theorem diagQuoted_computable :
    Computable fun p : ℕ × ℕ => (fun (_ n : ℕ) => witnessSentence n.unpair.1) p.1 p.2 :=
  (witnessSentence_computable.comp
    (Computable.fst.comp (Computable.unpair.comp Computable.snd))).of_eq fun _ => rfl

/-- `deferred_diagonal_subsequence`'s full hypothesis package at the paper pair, pairing
enumeration: for every `i`, the reader's day-`⟨i,k⟩` expectation of the day-`⟨i,k⟩` contract
tends in `k` to the fixed market's limiting belief in `witnessSentence i`. -/
theorem paperDeferred_diagonal (i : ℕ) :
    Tendsto (fun k => (ledgerLuv 0 (Nat.pair i k)).expect
      (deferredReader (paperDP 𝗜𝚺₁) (paperDP 𝗜𝚺₁) witnessLookahead
        (fun _ n => witnessSentence n.unpair.1) witnessSchedule) (Nat.pair i k)) atTop
      (𝓝 (limitingBelief (liaHistory (paperDP 𝗜𝚺₁)) (witnessSentence i))) :=
  haveI := deferred_inductor (paperDP 𝗜𝚺₁) (paperDP 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁)
    (paperDP_computable 𝗜𝚺₁) witnessLookahead witnessLookahead_computable
    (fun _ n => witnessSentence n.unpair.1) diagQuoted_computable witnessSchedule
    witnessSchedule_computable
  deferred_diagonal_subsequence (paperDP 𝗜𝚺₁) (paperDP 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁)
    witnessLookahead witnessLookahead_le witnessSentence witnessSchedule _
    (processFreeOf_ledgerSchedule_of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁))
    (paperDP_hworld 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁) i

end Cleanroom.Deference.DefTrackingPin
