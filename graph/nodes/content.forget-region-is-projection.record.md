---
id: content.forget-region-is-projection.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.Forgetting.forget_region
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: content.forget-region-is-projection
---
## Statement
The declaration Workspace.Normativity.Contrib.Forgetting.forget_region is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `content.forget-region-is-projection` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 134).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.Forgetting.forget_region` (theorem) in lean/Workspace/Normativity/Contrib/Forgetting.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {Q : Type*} (k : Fin (d + 1)) (B : Bundle Q (d + 1)) (x : Fin d → ℚ) :
        (forget k B).Region x ↔ projection k.succAbove B.Region x
