---
id: precedent.consistent-iff-pairwise.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.PrecedentConstraint.consistent_iff_pairwise
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: precedent.consistent-iff-pairwise
---
## Statement
The declaration Workspace.Normativity.Contrib.PrecedentConstraint.consistent_iff_pairwise is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `precedent.consistent-iff-pairwise` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 117).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.PrecedentConstraint.consistent_iff_pairwise` (theorem) in lean/Workspace/Normativity/Contrib/PrecedentConstraint.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (Γ : List (Case d)) :
        Consistent Γ ↔
          ∀ c ∈ Γ, ∀ c' ∈ Γ, ¬ (Covers c.losers c'.winners ∧ Covers c'.losers c.winners)
