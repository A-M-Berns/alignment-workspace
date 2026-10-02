import Cleanroom.Bli.BliCoherentMm.Contrast

/-!
Audit round 1, adversarial lens — positive probe for T1/T2/T4(c): the record **maker** (not only
a hypothetical accepted vector) is pinned near `1/2` on the responsive strategy, and at `ε = 0`
the only coherently accepted price is exactly `1/2`. So `coherent_fixed_point`'s conclusion is not
satisfied by the Dirac on any world (which prices the atom at `0` or `1`) — the fixed point is a
genuine interior point, and the maker's output exercises it. The package states
`responsive_near_half` for a hypothetical `hacc`; this instantiates it at `coherentWeights`.
Not imported by the library.
-/

namespace Cleanroom.Bli.BliCoherentMm.AuditR1Adv

open LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliOverlay

/-- The record maker on the responsive strategy prices `atom a` within `ε` of `1/2`
(`a < B`, empty stage). -/
theorem coherentWeights_responsive_near_half (a n : ℕ) (past : List RationalBeliefState) (B : ℕ)
    (hB : a < B) {ε : ℚ} (hε : 0 < ε) :
    |marginal (coherentWeights (responsiveStrategy n (Formula.atom a)) past ∅ B
        (mentionedSet (responsiveStrategy n (Formula.atom a))) subset_rfl (hW_empty B) hε)
        (Formula.atom a) - 1 / 2| ≤ ε :=
  responsive_near_half subset_rfl past hε.le
    (coherentWeights_accepts (responsiveStrategy n (Formula.atom a)) past ∅ B _ subset_rfl
      (hW_empty B) hε)
    ⟨fun _ => true, AttemptA.mem_WD_empty _, AttemptA.holds_atom_allTrue hB⟩
    ⟨fun _ => false, AttemptA.mem_WD_empty _, AttemptA.not_holds_atom_allFalse⟩

/-- At `ε = 0` the only coherently accepted price of `atom a` against the responsive strategy is
exactly `1/2`. -/
theorem coherentAccepts_responsive_zero_eq_half (a n : ℕ) (past : List RationalBeliefState)
    (B : ℕ) (hB : a < B) (S : Finset Sentence)
    (hS : mentionedSet (responsiveStrategy n (Formula.atom a)) ⊆ S) {w : FiniteWorld B → ℚ}
    (hacc : CoherentAccepts (responsiveStrategy n (Formula.atom a)) past ∅ B S 0 w) :
    marginal w (Formula.atom a) = 1 / 2 := by
  have h := responsive_near_half hS past le_rfl hacc
    ⟨fun _ => true, AttemptA.mem_WD_empty _, AttemptA.holds_atom_allTrue hB⟩
    ⟨fun _ => false, AttemptA.mem_WD_empty _, AttemptA.not_holds_atom_allFalse⟩
  have h0 : |marginal w (Formula.atom a) - 1 / 2| = 0 := le_antisymm h (abs_nonneg _)
  rw [abs_eq_zero, sub_eq_zero] at h0
  exact h0

end Cleanroom.Bli.BliCoherentMm.AuditR1Adv
