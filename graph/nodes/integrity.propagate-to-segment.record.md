---
id: integrity.propagate-to-segment.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.OpenIntegrityEvolution.Evolution.propagate_toSegment
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: integrity.propagate-to-segment
---
## Statement
The declaration Workspace.Normativity.Contrib.OpenIntegrityEvolution.Evolution.propagate_toSegment is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `integrity.propagate-to-segment` (class lean-proved, status active, origin round 2026-09-07-final-pressure-pass; answers item 78).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/THEOREMS.md; context: projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/READINESS.md.
The signature of `Workspace.Normativity.Contrib.OpenIntegrityEvolution.Evolution.propagate_toSegment` (theorem) in lean/Workspace/Normativity/Contrib/OpenIntegrityEvolution.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {O₀ O₁ : ObligationState S anchor}
        (ev : Evolution S anchor O₀ O₁) :
        ev.toSegment.propagate O₀.account = O₁.account
