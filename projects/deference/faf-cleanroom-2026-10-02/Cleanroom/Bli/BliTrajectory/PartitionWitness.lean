import Cleanroom.Bli.BliTrajectory.Coherent

/-!
# `bli-trajectory` · PartitionWitness: `e4_iff_partition_mass`'s hypothesis package is inhabited
(repair round 2)

Adopted from audit r2's adversarial probe `audit-r2-probes/PartitionWitness.lean` (N1). The
ledger row for `Partition.e4_iff_partition_mass` said no witness of its hypothesis package was
shipped (audit r1 fidelity N2; repair round 1 "not done"). The package is inhabited at every day
`n ≥ 1`: the market `pwHistory n` is the mixture, weights `½`, of two FAF worlds —
`cohWorld n 0` (holds `cohAtom` and `σ_{n+1,c₁}`) and `cohWorld n 3` (holds `σ_{n+1,c₂}` only)
— and `pwSystem`'s day-`(n+1)` tables are those two worlds' payouts. Then
`CoherentOn ∅ (pcpAtoms …) (𝐏_n)`, exclusivity and constraint 2 on **all** of `smallSet n` hold
(`partition_package_inhabited`), and the theorem's (⇐) direction yields `E4` at `n` from the
partition mass `1` (`e4_at_witness`). N+ on the coordinate that matters: two distinct charged
states (`½` each) with *different* tables (`cohAtom ↦ 1` vs `0`) and a market genuinely
uncertain about `cohAtom` (`½`).
-/

namespace Cleanroom.Bli.BliTrajectory

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite

open Classical

noncomputable section

/-- The two-world market: weights `½` on `cohWorld n 0` and `cohWorld n 3`.
Source: audit r2 adversarial N1 (probe `PartitionWitness.lean`); mandate M4
Kind: D
Fidelity: n/a -/
def pwHistory : History := fun n χ =>
  (1 / 2 : ℝ) * (cohWorld n 0).payout χ + (1 / 2 : ℝ) * (cohWorld n 3).payout χ

/-- Its state system: the day-`m` table of `c₁` is world `0`'s payout, of `c₂` world `3`'s (the
worlds of day `m − 1`, which hold the day-`m` state atoms; `m − 1` is `Nat` subtraction, and no
predicate reads a day-`0` table).
Source: audit r2 adversarial N1 (probe `PartitionWitness.lean`); mandate M4
Kind: D
Fidelity: n/a -/
def pwSystem : StateSystem where
  states := twoCodes
  val m q φ := if q = c₁ m then (cohWorld (m - 1) 0).payout φ else (cohWorld (m - 1) 3).payout φ
  actual m := 4 ^ sizeBound m
  actual_mem _ := by simp [twoCodes]

/-- The table of `c₁`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pwSystem_val₁ (n : ℕ) (φ : Sentence) :
    pwSystem.val (n + 1) (c₁ (n + 1)) φ = (cohWorld n 0).payout φ := by
  simp [pwSystem]

/-- The table of `c₂`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pwSystem_val₂ (n : ℕ) (φ : Sentence) :
    pwSystem.val (n + 1) (c₂ (n + 1)) φ = (cohWorld n 3).payout φ := by
  simp [pwSystem, (c₁_ne_c₂ (n + 1)).symm]

/-- **The hypothesis package of `e4_iff_partition_mass` is inhabited**, with the N+ certificate:
coherence on `pcpAtoms` (any stage, here `∅`), exclusivity, constraint 2 on all of `smallSet n`,
masses `½`, `½`, market `½` on `cohAtom`, tables `1`/`0` on `cohAtom`.
Source: audit r2 adversarial N1 (probe `PartitionWitness.lean`); mandate M4
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem partition_package_inhabited (n : ℕ) :
    CoherentOn ∅ (pcpAtoms pwSystem (fun _ => n + 1) n) (pwHistory n) ∧
    (∀ q₁ ∈ pwSystem.states (n + 1), ∀ q₂ ∈ pwSystem.states (n + 1), q₁ ≠ q₂ →
      pwHistory n (stateAtom (n + 1) q₁ ⋏ stateAtom (n + 1) q₂) = 0) ∧
    (∀ q ∈ pwSystem.states (n + 1), ∀ φ ∈ smallSet n,
      pwHistory n (φ ⋏ stateAtom (n + 1) q) =
        pwSystem.val (n + 1) q φ * pwHistory n (stateAtom (n + 1) q)) ∧
    pwHistory n (stateAtom (n + 1) (c₁ (n + 1))) = 1 / 2 ∧
    pwHistory n (stateAtom (n + 1) (c₂ (n + 1))) = 1 / 2 ∧
    pwHistory n cohAtom = 1 / 2 ∧
    pwSystem.val (n + 1) (c₁ (n + 1)) cohAtom = 1 ∧
    pwSystem.val (n + 1) (c₂ (n + 1)) cohAtom = 0 := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩ := cohWorld_payout_state n
  obtain ⟨t0, t1, t2, t3⟩ := cohWorld_payout_cohAtom n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨2, ![cohWorld n 0, cohWorld n 3], ![1 / 2, 1 / 2], fun i φ h => by simp at h,
      ?_, ?_, fun φ _ => ?_⟩
    · intro i; fin_cases i <;> norm_num
    · simp [Fin.sum_univ_two]; norm_num
    · simp [pwHistory, Fin.sum_univ_two]
  · intro q₁ hq₁ q₂ hq₂ hne
    simp only [pwSystem, twoCodes_eq, Finset.mem_insert, Finset.mem_singleton] at hq₁ hq₂
    rcases hq₁ with rfl | rfl <;> rcases hq₂ with rfl | rfl
    · exact absurd rfl hne
    · simp only [pwHistory]; rw [payout_and, payout_and, a0, b0, a3, b3]; ring
    · simp only [pwHistory]; rw [payout_and, payout_and, a0, b0, a3, b3]; ring
    · exact absurd rfl hne
  · intro q hq φ _
    simp only [pwSystem, twoCodes_eq, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · rw [pwSystem_val₁]; simp only [pwHistory]; rw [payout_and, payout_and, a0, a3]; ring
    · rw [pwSystem_val₂]; simp only [pwHistory]; rw [payout_and, payout_and, b0, b3]; ring
  · simp only [pwHistory]; rw [a0, a3]; norm_num
  · simp only [pwHistory]; rw [b0, b3]; norm_num
  · simp only [pwHistory]; rw [t0, t3]; norm_num
  · rw [pwSystem_val₁, t0]
  · rw [pwSystem_val₂, t3]

/-- **The theorem applied at the witness**: constraint 4 at `n ≥ 1` holds because the partition
mass is `1` — the (⇐) direction of `e4_iff_partition_mass`, exercised.
Source: audit r2 adversarial N1 (probe `PartitionWitness.lean`); mandate M4
Kind: C
Fidelity: exact
Hyps: (a) `1 ≤ n` -/
theorem e4_at_witness (n : ℕ) (hn : 1 ≤ n) :
    ∀ φ ∈ smallSet n,
      pwHistory n φ = ∑ q ∈ pwSystem.states (n + 1),
        pwHistory n (stateAtom (n + 1) q) * pwSystem.val (n + 1) q φ := by
  obtain ⟨hcoh, hexcl, hE2, h1, h2, -⟩ := partition_package_inhabited n
  refine (e4_iff_partition_mass pwSystem pwHistory n hn ∅ hcoh hexcl hE2).mpr ?_
  show ∑ q ∈ twoCodes (n + 1), pwHistory n (stateAtom (n + 1) q) = 1
  rw [twoCodes_eq, Finset.sum_pair (c₁_ne_c₂ _), h1, h2]; norm_num

end

end Cleanroom.Bli.BliTrajectory
