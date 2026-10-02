import Cleanroom.Bli.BliLinkage.InstanceK3Local

/-!
# Audit round 4 (adversarial) — probe: the local K3 package's content on the stage side

Evidence for [[bli-linkage-audit-r4-adversarial]] N3. Repair round 3 answered audit r3
fidelity N5 by one prose sentence in `no_degenerate_linked_bli`'s docstring ("a moved day whose
refuting stage is `≤ n` is contradicted by stage coherence alone"). This file checks it for the
local form of record (`E1xLit`), where it matters more: the local package is the only K3
instance at FAF's LIA with content, and the question is where that content lives.

1. `lit_package_stage_consistent`: under `PCPσ ∧ E5σ ∧ Degenerate` (no base, no `E1x` of any
   kind), on every pinned day the degenerate table's literal `lit_{n+1, c, t}` is held by a
   world consistent with the day-`n` stage. So the superbelief side of the package already
   forbids the stage from refuting tomorrow's literal of today's cell.
2. `lit_package_contradicts_early_refutation`: hence a moved day whose refuting stage `k` (the
   `hdec` witness) satisfies `k ≤ n` contradicts the package with no inductor and no trader;
   `no_degenerate_linked_bli_lit`'s exploitation argument carries the theorem only for moved
   days whose literal is refuted after day `n`.

Not imported by the library. Elaborated with `scripts/lean-check`.
-/

namespace Cleanroom.Bli.BliLinkage.AuditR4

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound
open Cleanroom.Bli.BliLinkage
open Cleanroom.Bli.BliLinkageB (payout_of_holds payout_of_not_holds atoms_subset_smallAtoms)

variable {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) {S : StateSystem} {atoms : ℕ → Finset ℕ}
variable {DP : DeductiveProcess} {P : History} {index : ℕ → List ℕ}

/-- 1. On a pinned day the degenerate literal is held by some world consistent with the
day-`n` stage (superbelief side only: `PCPσ ∧ E5σ ∧ Degenerate`, no base). -/
theorem lit_package_stage_consistent (hcoh : PCPσ atoms DP P)
    (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n) (hE5 : E5σ (stateOf C) S P)
    {deg : ℕ → ℕ} (hdegS : ∀ n, deg n ∈ S.states (n + 1)) (hdeg : Degenerate (stateOf C) P deg)
    (n : ℕ) (hsp : SpuriousEntails (stateOf C) C.literal S index C.cells n) {c : ℕ}
    (hc : c ∈ pinned C index n) {t : ℕ} (hentry : entryOf c (tableOfCode (deg n)) = some t)
    (ht : t ∈ C.cells (n + 1)) :
    ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧
      v.Holds (C.literal (n + 1) (sentenceOfCode c) t) := by
  have h1 := degenerate_literal_indicator C hcoh hatoms hE5 (Q := P) (fun _ _ _ => rfl) hdegS
    hdeg n hsp hc hentry ht
  rw [if_pos rfl] at h1
  have hsmall : C.literal (n + 1) (sentenceOfCode c) t ∈ smallSet n := by
    rw [mem_smallSet]; exact ((mem_pinned C index n c).1 hc).2 t ht
  obtain ⟨k, W, w, hW, hw, hsum, hrep⟩ := hcoh n
  rw [hrep _ ((atoms_subset_smallAtoms hsmall).trans Finset.subset_union_left)] at h1
  by_contra hno
  push Not at hno
  have hzero : ∑ i, w i * (W i).payout (C.literal (n + 1) (sentenceOfCode c) t) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      rw [payout_of_not_holds (hno (W i) (hW i)), mul_zero]
  rw [hzero] at h1
  norm_num at h1

/-- 2. A moved day refuted by a stage `k ≤ n` contradicts the package by stage coherence
alone (FAF's stages are nondecreasing). -/
theorem lit_package_contradicts_early_refutation (hcoh : PCPσ atoms DP P)
    (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n) (hE5 : E5σ (stateOf C) S P)
    {deg : ℕ → ℕ} (hdegS : ∀ n, deg n ∈ S.states (n + 1)) (hdeg : Degenerate (stateOf C) P deg)
    (n : ℕ) (hsp : SpuriousEntails (stateOf C) C.literal S index C.cells n) {c : ℕ}
    (hc : c ∈ pinned C index n) {t : ℕ} (hentry : entryOf c (tableOfCode (deg n)) = some t)
    (ht : t ∈ C.cells (n + 1)) {k : ℕ} (hk : k ≤ n)
    (hdec : ∀ v : PCWorld, v.ConsistentWith (DP.D k) →
      ¬ v.Holds (C.literal (n + 1) (sentenceOfCode c) t)) : False := by
  obtain ⟨v, hv, hlit⟩ :=
    lit_package_stage_consistent C hcoh hatoms hE5 hdegS hdeg n hsp hc hentry ht
  have hmono : DP.D k ≤ DP.D n := monotone_nat_of_le_succ (f := DP.D) DP.mono hk
  exact hdec v (fun φ hφ => hv φ (hmono hφ)) hlit

end Cleanroom.Bli.BliLinkage.AuditR4
