---
id: rebuttal.settleform-sound.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.WarrantEntitlement.settleForm_eq_some_iff
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: rebuttal.settleform-sound
---
## Statement
The declaration Workspace.Normativity.Contrib.WarrantEntitlement.settleForm_eq_some_iff is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `rebuttal.settleform-sound` (class lean-proved, status active, origin round 2026-10-21-rebuttal-and-end-to-end; answers item 113).
Documentation: verification: projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/REBUTTAL.md; context: projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/REBUTTAL.md.
The signature of `Workspace.Normativity.Contrib.WarrantEntitlement.settleForm_eq_some_iff` (theorem) in lean/Workspace/Normativity/Contrib/WarrantEntitlement.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (F : Settlement d) (o : Occurrence d) (rows : List (Row d)) :
        settleForm F o = some rows ↔ rows = [specialize F o.form.row] ∧ ¬ Degenerate F o.form
