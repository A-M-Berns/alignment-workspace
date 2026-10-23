---
id: warrant.selection-not-transparent.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.selection_not_transparent
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: warrant.selection-not-transparent
---
## Statement
The declaration Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.selection_not_transparent is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `warrant.selection-not-transparent` (class lean-proved, status active, origin round 2026-10-20-warrant-enforcement-semantics; answers item 56).
Documentation: verification: projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/LICENCE_CHAIN.md; context: projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/COUNTERMODELS.md.
The signature of `Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.selection_not_transparent` (theorem) in lean/Workspace/Normativity/Contrib/WarrantEntitlement.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (κ : Party → Unit → Unit → List ℚ) :
        ¬ TransparentAt interface frame κ 0
