---
id: standing.reallocated-entitles-nothing.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.AdmissionByStanding.reallocated_entitles_nothing
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: standing.reallocated-entitles-nothing
---
## Statement
The declaration Workspace.Normativity.Contrib.AdmissionByStanding.reallocated_entitles_nothing is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `standing.reallocated-entitles-nothing` (class lean-proved, status active, origin round 2026-11-07-score-side-binding; answers item 128).
Documentation: verification: projects/normativity/rounds/2026-11-07-score-side-binding/THEOREM.md; context: projects/normativity/rounds/2026-11-07-score-side-binding/REPORT.md.
The signature of `Workspace.Normativity.Contrib.AdmissionByStanding.reallocated_entitles_nothing` (theorem) in lean/Workspace/Normativity/Contrib/AdmissionByStanding.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (O : ObligationState protocolS₁ wAnchor)
        (Expresses : Unit → SeedStatics.Form 5 → Prop) (E : Entitlement O grounds Expresses)
        (o : WarrantEntitlement.Occurrence 5) (ho : o ∈ grounds) : E.origin o ≠ 0
