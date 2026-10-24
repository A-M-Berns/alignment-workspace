---
id: maxmin.representation.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.MaxMinRepresentation.exists_maxMin_representation
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: maxmin.representation
---
## Statement
The declaration Workspace.Normativity.Contrib.MaxMinRepresentation.exists_maxMin_representation is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `maxmin.representation` (class lean-proved, status active, origin round 2026-08-18-maxmin-representation; answers item 50).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-18-maxmin-representation/README.md.
The signature of `Workspace.Normativity.Contrib.MaxMinRepresentation.exists_maxMin_representation` (theorem) in lean/Workspace/Normativity/Contrib/MaxMinRepresentation.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    [Finite ι] {Γ : Set E} {f : E → ℝ}
        {g : ι → E →ᵃ[ℝ] ℝ} (hΓ : Convex ℝ Γ) (hne : Γ.Nonempty)
        (hf : IsPiecewiseAffineOn Γ f g) :
        ∃ (m : ℕ) (S : Fin (m + 1) → Finset ι) (hS : ∀ j, (S j).Nonempty),
          ∀ x ∈ Γ, f x = Finset.univ.sup' Finset.univ_nonempty
            fun j => (S j).inf' (hS j) fun i => g i x
