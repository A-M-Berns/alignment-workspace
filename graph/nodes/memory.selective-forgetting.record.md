---
id: memory.selective-forgetting.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.Forgetting.selective_forgetting
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: memory.selective-forgetting
---
## Statement
The declaration Workspace.Normativity.Contrib.Forgetting.selective_forgetting is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `memory.selective-forgetting` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 135).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.Forgetting.selective_forgetting` (theorem) in lean/Workspace/Normativity/Contrib/Forgetting.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    :
        (IsInterval (afterForget 1 1 later) 0 0 1 ∧ IsInterval (afterForget 2 2 later) 0 0 1) ∧
        (IsInterval (afterForget 2 1 later) 0 (3/4) 1 ∧ IsInterval (afterForget 1 2 later) 0 (3/4) 1) ∧
        (IsForcedInterval (recOn 1) [] DocketState.quiet bothTrue 0 (3/4) 1 ∧
          IsForcedInterval (recOn 2) [] DocketState.quiet bothTrue 0 (3/4) 1)
