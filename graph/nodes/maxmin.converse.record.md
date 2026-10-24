---
id: maxmin.converse.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.MaxMinRepresentation.isPiecewiseAffineOn_maxMin
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: maxmin.converse
---
## Statement
The declaration Workspace.Normativity.Contrib.MaxMinRepresentation.isPiecewiseAffineOn_maxMin is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `maxmin.converse` (class lean-proved, status active, origin round 2026-08-18-maxmin-representation; answers item 50).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-18-maxmin-representation/README.md.
The signature of `Workspace.Normativity.Contrib.MaxMinRepresentation.isPiecewiseAffineOn_maxMin` (theorem) in lean/Workspace/Normativity/Contrib/MaxMinRepresentation.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    [Finite ι] {Γ : Set E} {g : ι → E →ᵃ[ℝ] ℝ}
        (hg : ∀ i, Continuous (g i)) {m : ℕ} (S : Fin (m + 1) → Finset ι)
        (hS : ∀ j, (S j).Nonempty) :
        IsPiecewiseAffineOn Γ
          (fun x => Finset.univ.sup' Finset.univ_nonempty fun j => (S j).inf' (hS j) fun i => g i x)
          g
