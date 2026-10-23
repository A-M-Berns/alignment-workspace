---
id: warrant.supported-not-licensed.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.supported_not_licensed
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: warrant.supported-not-licensed
---
## Statement
The declaration Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.supported_not_licensed is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `warrant.supported-not-licensed` (class lean-proved, status active, origin round 2026-10-20-warrant-enforcement-semantics; answers item 56).
Documentation: verification: projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/LICENCE_CHAIN.md; context: projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/COUNTERMODELS.md.
The signature of `Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.supported_not_licensed` (theorem) in lean/Workspace/Normativity/Contrib/WarrantEntitlement.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    :
        Supported G DocketState.quiet F φ (2/3) (cert 1) ∧
        Supported G DocketState.quiet F φ (3/4) (cert 1) ∧
        Licensed recordAuth φ (2/3) (cert 1) 7 ∧
        ¬ Licensed recordNoAuth φ (3/4) (cert 1) 7
