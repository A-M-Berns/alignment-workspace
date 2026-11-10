---
id: precedent.assessor-sets-precedent.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.AssessedConduct.assessor_sets_precedent
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: precedent.assessor-sets-precedent
---
## Statement
The declaration Workspace.Normativity.Contrib.AssessedConduct.assessor_sets_precedent is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `precedent.assessor-sets-precedent` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 117).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.AssessedConduct.assessor_sets_precedent` (theorem) in lean/Workspace/Normativity/Contrib/AssessedConduct.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (v : Verdict) :
        ¬ Permitted [first.case] (again v).proposal ∧ Permitted [first.proposal] (again v).proposal
