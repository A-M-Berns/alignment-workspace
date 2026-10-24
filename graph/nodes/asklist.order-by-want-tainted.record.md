---
id: asklist.order-by-want-tainted.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.AskList.Rows3.order_by_want_tainted
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: asklist.order-by-want-tainted
---
## Statement
The declaration Workspace.Deference.Contrib.AskList.Rows3.order_by_want_tainted is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `asklist.order-by-want-tainted` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/FOLLOWUP.md.
The signature of `Workspace.Deference.Contrib.AskList.Rows3.order_by_want_tainted` (theorem) in lean/Workspace/Deference/Contrib/AskListDimension.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    :
        ¬ Counted3 rowOrder state₀ (stAdmit false) ∧
          deviates3 rowOrder.decl (Policy3.orderByWant.present rowOrder.decl true) = true
