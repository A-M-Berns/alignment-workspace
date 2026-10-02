import Cleanroom.Trust.LegitLiRegister.Schedule

/-!
# Audit r3 (adversarial) probe · the bridge is process-blind beyond the completed theory

`truthProcess_bridge_ofComputation` is stated over the scheduled process `truthProcess DP x g`.
This probe re-runs its proof over an **arbitrary** process `DP'` with only `TheoryTruth` (every
completed-theory world pays the truth) and satisfiable stages — the two facts the constructor
reads — to make the package's "schedule-blind" literal: the `FeedbackTruthSequence` never sees
which stage decides an item, only the completed theory. Two corollaries at the package's own
N+ (`truthProcess_bridge_alternating_lia_double`, FAF's LIA over the `doubleDelay` schedule):
the *same market* carries the bridge over the truth-independent schedule `g ≡ 0` and over the
schedule `g n := n ^ n` — nothing in the bridge records which process the market was built
over. Not imported by the library.
-/

namespace Cleanroom.Trust.LegitLiRegister.AuditR3

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound AffineCombination

/-- The constructor route, over any process: `TheoryTruth` + satisfiable stages + `[0,1]` prices +
a `FeedbackTruthComputation` give the bridge. The scheduled process plays no role. -/
theorem bridge_of_theoryTruth (DP' : DeductiveProcess) (truth : ℕ → ℝ)
    (htruth : TheoryTruth schedAtom DP' truth)
    (hw : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP'.D n))
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (C : FeedbackTruth.FeedbackTruthComputation truth f)
    (P : History) (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) :
    Nonempty (FeedbackTruthSequence (sentenceAffine schedAtom) truth P DP' f) := by
  have hdet : DeterminedViaTheory (sentenceAffine schedAtom) P DP' truth := by
    intro n v hv
    simpa [sentenceAffine, AffineCombination.value] using htruth n v hv
  exact ⟨FeedbackTruth.feedbackTruthSequence_ofDetermined
    (sentenceAffine_polySequence schedAtom schedAtom_codes)
    (sentenceAffine_bounded schedAtom P hP) hdet C hstrict (fun n => by simp) hP hw⟩

/-- The N+'s market — FAF's LIA built over the `doubleDelay` schedule — carries the bridge over the
schedule with **no** delay (`g ≡ 0`, every item decided at `n + 1`). -/
theorem lia_double_bridges_zero_delay :
    Nonempty (FeedbackTruthSequence (sentenceAffine schedAtom)
      (FeedbackTruth.alternatingTruth succDeferral)
      (liaHistory (truthProcess (paperDP 𝗜𝚺₁) (altBool succDeferral) doubleDelay))
      (truthProcess (paperDP 𝗜𝚺₁) (altBool succDeferral) (fun _ => 0)) succDeferral) :=
  haveI := truthProcess_lia_inductor doubleDelay doubleDelay_primrec
  truthProcess_bridge_alternating (paperDP 𝗜𝚺₁)
    (paperDP_tagFree 𝗜𝚺₁ (by simp [cleanroomBaseTag])) (paperDP_hworld 𝗜𝚺₁) _ succDeferral
    succDeferral_strict _ (fun n φ => IsLogicalInductor.price_mem_Icc
      (DP := truthProcess (paperDP 𝗜𝚺₁) (altBool succDeferral) doubleDelay) n φ)

/-- …and over a (non-primitive-recursive-looking, still computable) tower delay `g n := n ^ n`,
for which no inductor is exhibited anywhere in the run. -/
theorem lia_double_bridges_tower_delay :
    Nonempty (FeedbackTruthSequence (sentenceAffine schedAtom)
      (FeedbackTruth.alternatingTruth succDeferral)
      (liaHistory (truthProcess (paperDP 𝗜𝚺₁) (altBool succDeferral) doubleDelay))
      (truthProcess (paperDP 𝗜𝚺₁) (altBool succDeferral) (fun n => n ^ n)) succDeferral) :=
  haveI := truthProcess_lia_inductor doubleDelay doubleDelay_primrec
  truthProcess_bridge_alternating (paperDP 𝗜𝚺₁)
    (paperDP_tagFree 𝗜𝚺₁ (by simp [cleanroomBaseTag])) (paperDP_hworld 𝗜𝚺₁) _ succDeferral
    succDeferral_strict _ (fun n φ => IsLogicalInductor.price_mem_Icc
      (DP := truthProcess (paperDP 𝗜𝚺₁) (altBool succDeferral) doubleDelay) n φ)

end Cleanroom.Trust.LegitLiRegister.AuditR3
