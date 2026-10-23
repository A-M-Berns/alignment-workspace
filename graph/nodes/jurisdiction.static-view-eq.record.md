---
id: jurisdiction.static-view-eq.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.StaticViewFactorization.staticView_eq
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: jurisdiction.static-view-eq
---
## Statement
The declaration Workspace.Deference.Contrib.StaticViewFactorization.staticView_eq is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `jurisdiction.static-view-eq` (class lean-proved, status active, origin round 2026-08-11-stage-v-li-native; answers item 28).
Documentation: verification: prompts/2026-08-11-stage-v-li-native/REPORT.md; context: prompts/2026-08-11-stage-v-li-native/REPORT.md.
The signature of `Workspace.Deference.Contrib.StaticViewFactorization.staticView_eq` (theorem) in lean/Workspace/Deference/Contrib/StaticViewFactorization.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {Price : Type uP} {Realization : Type uR}
        {left right : Price × Realization} (hprice : left.1 = right.1)
        (hrealization : left.2 = right.2) : left = right
