---
id: corrective.no-exclusive-effect.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.ReachableCorrectiveControl.principal_has_no_exclusive_effect
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: corrective.no-exclusive-effect
---
## Statement
The declaration Workspace.Deference.Contrib.ReachableCorrectiveControl.principal_has_no_exclusive_effect is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `corrective.no-exclusive-effect` (class lean-proved, status active, origin round 2026-08-12-reachable-corrective-control; answers item 60).
Documentation: verification: prompts/2026-08-12-reachable-corrective-control/REPORT.md; context: prompts/2026-08-12-reachable-corrective-control/REPORT.md.
The signature of `Workspace.Deference.Contrib.ReachableCorrectiveControl.principal_has_no_exclusive_effect` (theorem) in lean/Workspace/Deference/Contrib/ReachableCorrectiveControl.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    :
        ∀ (s : St) (h : HAct) (e : EAct), ∃ a : AAct, step s .idle a e = step s h .noop e
