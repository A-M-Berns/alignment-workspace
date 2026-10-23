---
id: open-integrity.answerable.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.OpenIntegrityEvolution.OpenIntegritySegment.answerable
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: open-integrity.answerable
---
## Statement
The declaration Workspace.Normativity.Contrib.OpenIntegrityEvolution.OpenIntegritySegment.answerable is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `open-integrity.answerable` (class lean-proved, status active, origin round 2026-09-07-final-pressure-pass; answers item 78).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/THEOREMS.md; context: projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/READINESS.md.
The signature of `Workspace.Normativity.Contrib.OpenIntegrityEvolution.OpenIntegritySegment.answerable` (theorem) in lean/Workspace/Normativity/Contrib/OpenIntegrityEvolution.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {O₀ O₁ : ObligationState S anchor}
        (seg : OpenIntegritySegment S anchor sem O₀ O₁) :
        Conservation S anchor O₀ O₁ ∧ OpenAt sem O₀ ∧ OpenAt sem O₁
