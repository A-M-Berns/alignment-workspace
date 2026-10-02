import Cleanroom.Bli.BliTrajectory.Pinning
import Cleanroom.Bli.BliTrajectory.PartitionWitness

/-!
# Audit r3 (adversarial) probe — `bli-trajectory`: `Pinning.two_state_pinning_scope`'s
hypothesis package is inhabited (at `PartitionWitness.pwSystem`, scope = every sentence)

Not imported by the library. The ledger's Witness column for the Pinning rows says "n/a (a
positive result; its hypotheses are met by any two-state world-mixture system with distinct
tables, e.g. `PartitionWitness.pwSystem`'s two worlds at `(n, n+1)` on the cell algebra)" —
prose, not Lean. This probe discharges every hypothesis of `two_state_pinning_scope` at
`pwSystem` / `pwHistory n` with `Γ := Set.univ` and `φ := cohAtom` (tables `1` vs `0`), and
reads off the conclusion. N+ on the coordinate the theorem is about: two charged states (`½`
each) with distinct tables and a market uncertain about `cohAtom`. The tables are `0/1`-valued
(single worlds), which is the degenerate side of the witness.
-/

namespace Cleanroom.Bli.BliTrajectory.AuditR3

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory

open Classical

noncomputable section

/-- `payout (∼φ) = 1 − payout φ` (from FAF's `holds_neg`). -/
lemma payout_neg' (v : PCWorld) (φ : Sentence) : v.payout (∼φ) = 1 - v.payout φ := by
  unfold PCWorld.payout
  by_cases h : v.Holds φ <;> simp [PCWorld.holds_neg, h]

/-- Every `pwSystem` table is a world payout. -/
lemma pwSystem_val_eq (m q : ℕ) :
    ∃ v : PCWorld, ∀ φ, pwSystem.val m q φ = v.payout φ := by
  by_cases hq : q = c₁ m
  · exact ⟨cohWorld (m - 1) 0, fun φ => by simp [pwSystem, hq]⟩
  · exact ⟨cohWorld (m - 1) 3, fun φ => by simp [pwSystem, hq]⟩

/-- Constraint 2 at `(n, n+1)` on **every** sentence for `pwHistory n` (the proof of
`partition_package_inhabited`'s third conjunct never used `φ ∈ smallSet n`). -/
lemma pw_cond2_all (n : ℕ) (q : ℕ) (hq : q ∈ pwSystem.states (n + 1)) (φ : Sentence) :
    pwHistory n (φ ⋏ stateAtom (n + 1) q) =
      pwSystem.val (n + 1) q φ * pwHistory n (stateAtom (n + 1) q) := by
  obtain ⟨⟨a0, -, -, a3⟩, ⟨b0, -, -, b3⟩⟩ := cohWorld_payout_state n
  simp only [pwSystem, twoCodes_eq, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · rw [pwSystem_val₁]; simp only [pwHistory]; rw [payout_and, payout_and, a0, a3]; ring
  · rw [pwSystem_val₂]; simp only [pwHistory]; rw [payout_and, payout_and, b0, b3]; ring

/-- Faith in the marginal at `(n, n+1)` on every sentence, from constraint 2. -/
lemma pw_faith_all (n : ℕ) (χ : Sentence) (x : ℝ) :
    marginalJoint pwSystem pwHistory n (n + 1) χ x =
      x * marginalMass pwSystem pwHistory n (n + 1) χ x := by
  unfold marginalJoint marginalMass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.mem_filter] at hq
  rw [pw_cond2_all n q hq.1 χ, hq.2]

/-- **`two_state_pinning_scope` applied at the witness**: every hypothesis discharged, the
conclusion read off on every sentence. -/
theorem pinning_package_inhabited (n : ℕ) :
    ∀ χ, pwHistory n (χ ⋏ stateAtom (n + 1) (c₁ (n + 1))) =
        pwSystem.val (n + 1) (c₁ (n + 1)) χ * pwHistory n (stateAtom (n + 1) (c₁ (n + 1))) ∧
      pwHistory n (χ ⋏ stateAtom (n + 1) (c₂ (n + 1))) =
        pwSystem.val (n + 1) (c₂ (n + 1)) χ * pwHistory n (stateAtom (n + 1) (c₂ (n + 1))) := by
  obtain ⟨-, -, -, -, -, -, hv₁, hv₂⟩ := partition_package_inhabited n
  intro χ
  refine two_state_pinning_scope pwSystem pwHistory n (n + 1) (c₁ (n + 1)) (c₂ (n + 1))
    (twoCodes_eq _) (c₁_ne_c₂ _) Set.univ (fun _ _ _ _ => Set.mem_univ _)
    (fun _ _ => Set.mem_univ _) ?_ ?_ ?_ ?_ ?_ ?_ cohAtom (Set.mem_univ _) ?_ χ (Set.mem_univ _)
  · intro q φ _ χ _
    obtain ⟨v, hv⟩ := pwSystem_val_eq (n + 1) q
    rw [hv, hv, hv, payout_and, payout_and, payout_neg']; ring
  · intro q φ _
    obtain ⟨v, hv⟩ := pwSystem_val_eq (n + 1) q
    rw [hv, hv, payout_neg']
  · intro q φ _ χ _
    obtain ⟨v, hv⟩ := pwSystem_val_eq (n + 1) q
    rw [hv, hv, payout_and, payout_and]; ring
  · intro q φ _ χ _
    simp only [pwHistory, payout_and, payout_neg']
    ring
  · intro q φ _ χ _
    simp only [pwHistory, payout_and]
    ring
  · intro χ _ x
    exact pw_faith_all n χ x
  · rw [hv₁, hv₂]; norm_num

end

end Cleanroom.Bli.BliTrajectory.AuditR3
