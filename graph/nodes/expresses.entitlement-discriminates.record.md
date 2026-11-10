---
id: expresses.entitlement-discriminates.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.ExpressesByRole.entitlement_discriminates
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: expresses.entitlement-discriminates
---
## Statement
The declaration Workspace.Normativity.Contrib.ExpressesByRole.entitlement_discriminates is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `expresses.entitlement-discriminates` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 128).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.ExpressesByRole.entitlement_discriminates` (theorem) in lean/Workspace/Normativity/Contrib/ExpressesByRole.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    :
        Nonempty (Entitlement stateW [occ35] (ExpressesNoMore ι settled)) ∧
          IsEmpty (Entitlement stateW [occ35] (ExpressesNoMore ι plain)) ∧
          IsEmpty (Entitlement stateW groundsCh (ExpressesNoMore ι settled))
