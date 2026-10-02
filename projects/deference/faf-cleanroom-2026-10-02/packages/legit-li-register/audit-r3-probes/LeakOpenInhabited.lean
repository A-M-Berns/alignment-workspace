import Cleanroom.Trust.LegitLiRegister.Schedule

/-!
# Audit r3 (adversarial) probe · `schedule_leak_open` is a real open statement

Checks two things about the OPEN `schedule_leak_open` (Target 9 (ii)) that an open list cannot
show by itself: (1) its hypothesis package is **inhabited** — so it is not vacuously provable by
contradiction — and (2) at that inhabitant its conclusion **holds** (through the alternating
bridge), so the universal statement is not uniformly false either: its expected falsity, if any,
lives at a stream that is computable but not machine-computable along the deferral. The instance:
base `paperDP 𝗜𝚺₁`, the alternating stream at the successor deferral, delay profile `g ≡ 0`
(every item decided at `n + 1`), bound `B n := n + 1`, market FAF's LIA over the scheduled process.
Not imported by the library.
-/

namespace Cleanroom.Trust.LegitLiRegister.AuditR3

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound AffineCombination

/-- The delay/bound/deferral hypotheses of `schedule_leak_open` hold at `g ≡ 0`, `B := succ`,
`f := succDeferral`. -/
theorem leak_hyps_inhabited :
    (∀ n, (fun _ : ℕ => (0 : ℕ)) n ≤ (fun n => n + 1) n) ∧
    (∀ n, n + 1 ≤ (fun n => n + 1) n) ∧
    StrictlyIncreasingDeferral succDeferral ∧
    (∀ k, (fun n => n + 1) (succDeferral.f k) ≤ succDeferral.f (k + 1)) :=
  ⟨fun _ => Nat.zero_le _, fun _ => le_rfl, succDeferral_strict, fun _ => le_rfl⟩

/-- The inductor hypothesis of `schedule_leak_open` is inhabited at that instance by FAF's LIA. -/
theorem leak_inductor_inhabited :
    IsLogicalInductor (liaHistory (truthProcess (paperDP 𝗜𝚺₁) (altBool succDeferral) (fun _ => 0)))
      (truthProcess (paperDP 𝗜𝚺₁) (altBool succDeferral) (fun _ => 0)) :=
  truthProcess_lia_inductor _ (Primrec.const 0)

/-- At that instance the OPEN's conclusion holds (the alternating bridge at the LIA). -/
theorem leak_conclusion_at_instance :
    Nonempty (FeedbackTruthSequence (sentenceAffine schedAtom)
      (fun n => if altBool succDeferral n then (1 : ℝ) else 0)
      (liaHistory (truthProcess (paperDP 𝗜𝚺₁) (altBool succDeferral) (fun _ => 0)))
      (truthProcess (paperDP 𝗜𝚺₁) (altBool succDeferral) (fun _ => 0)) succDeferral) := by
  rw [altBool_truth]
  exact truthProcess_bridge_alternating_lia _ (Primrec.const 0)

end Cleanroom.Trust.LegitLiRegister.AuditR3
