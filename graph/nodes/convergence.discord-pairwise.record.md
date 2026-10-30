---
id: convergence.discord-pairwise.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.ConvergenceMeasure.discord_iff_pair
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: convergence.discord-pairwise
---
## Statement
The declaration Workspace.Normativity.Contrib.ConvergenceMeasure.discord_iff_pair is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `convergence.discord-pairwise` (class lean-proved, status active, origin round 2026-10-21-rebuttal-and-end-to-end; answers item 119).
Documentation: verification: projects/normativity/seed/rounds/2026-09-17-convergence-measure/MANY.md; context: projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/LANDING.md.
The signature of `Workspace.Normativity.Contrib.ConvergenceMeasure.discord_iff_pair` (theorem) in lean/Workspace/Normativity/Contrib/ConvergenceMeasure.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (I : IntervalData ι d) (φ : Fin d) :
        Discord I φ ↔ ∃ i j : ι, (I j φ).2 < (I i φ).1
