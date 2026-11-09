---
id: content.licensed-no-challenge.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.VocabularyAct.licensed_no_challenge
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: content.licensed-no-challenge
---
## Statement
The declaration Workspace.Normativity.Contrib.VocabularyAct.licensed_no_challenge is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `content.licensed-no-challenge` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 134).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.VocabularyAct.licensed_no_challenge` (theorem) in lean/Workspace/Normativity/Contrib/VocabularyAct.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (V : VocabularyChange A d d') (h : Licensed V)
        (c : Challenge d d') : ¬ c.Valid V V.fragment
