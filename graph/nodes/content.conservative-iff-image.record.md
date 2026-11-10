---
id: content.conservative-iff-image.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.Conservativity.conservative_iff
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: content.conservative-iff-image
---
## Statement
The declaration Workspace.Normativity.Contrib.Conservativity.conservative_iff is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `content.conservative-iff-image` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 134).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.Conservativity.conservative_iff` (theorem) in lean/Workspace/Normativity/Contrib/Conservativity.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (T : Translation d d') (B : Bundle Q d) (B' : Bundle Q' d') :
        Conservative T B.Region B'.Region ↔ ∀ x, image T B'.Region x ↔ B.Region x
