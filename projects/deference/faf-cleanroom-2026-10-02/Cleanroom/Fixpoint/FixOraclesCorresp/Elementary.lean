import Mathlib.Data.Set.Image
import Mathlib.Dynamics.FixedPoints.Basic

/-!
# `Cleanroom.Fixpoint.FixOraclesCorresp.Elementary`: the two elementary facts of fixpoint-lit-013

The Discord thread's "computation as nested intersections" and "forward and back" remarks contain
exactly two precise statements, both elementary (mandate Part A, no headline rows): `f (f⁻¹ A) ⊆ A ⊆
f⁻¹ (f A)`, and a closed `C` with `f C ∩ C = ∅` contains no fixed point of `f` (so a shrinking family
of such `C` gives a nested family of sets containing `Fix f`).
-/

namespace Cleanroom.Fixpoint.FixOraclesCorresp

open Set

/-- "If you go forward and back you might gain points, but if you go back and forward you recover":
`f '' (f ⁻¹' A) ⊆ A` and `A ⊆ f ⁻¹' (f '' A)` (Mathlib's `Set.image_preimage_subset` and
`Set.subset_preimage_image`).
Source: [[fixpoint-lit-inventory]] 013 (discord-notes "Brouwer and Computation")
Kind: L
Fidelity: exact
Hyps: none -/
theorem image_preimage_subset_subset_preimage_image {α β : Type*} (f : α → β) (A : Set β)
    (C : Set α) : f '' (f ⁻¹' A) ⊆ A ∧ C ⊆ f ⁻¹' (f '' C) :=
  ⟨Set.image_preimage_subset f A, Set.subset_preimage_image f C⟩

/-- "We can still point out a tightening set that contains the fixed points": if `f '' C ∩ C = ∅` then
`C` contains no fixed point of `f`.
Source: [[fixpoint-lit-inventory]] 013 (discord-notes "Computation as Nested Intersections")
Kind: L
Fidelity: exact
Hyps: none -/
theorem fixedPoints_disjoint_of_image_disjoint {α : Type*} (f : α → α) (C : Set α)
    (h : f '' C ∩ C = ∅) : Function.fixedPoints f ∩ C = ∅ := by
  ext x
  simp only [mem_inter_iff, Function.mem_fixedPoints, Function.IsFixedPt, mem_empty_iff_false,
    iff_false, not_and]
  intro hx hC
  have : f x ∈ f '' C ∩ C := ⟨⟨x, hC, rfl⟩, by rw [hx]; exact hC⟩
  rw [h] at this
  exact this

end Cleanroom.Fixpoint.FixOraclesCorresp
