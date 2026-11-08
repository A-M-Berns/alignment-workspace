---
id: solvency.bounded-iff-frequency.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.WarrantSolvency.Schema.bounded_iff_frequency
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: solvency.bounded-iff-frequency
---
## Statement
The declaration Workspace.Normativity.Contrib.WarrantSolvency.Schema.bounded_iff_frequency is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `solvency.bounded-iff-frequency` (class lean-proved, status active, origin round 2026-11-07-score-side-binding; answers item 61).
Documentation: verification: projects/normativity/rounds/2026-11-07-score-side-binding/THEOREM.md; context: projects/normativity/rounds/2026-11-07-score-side-binding/REPORT.md.
The signature of `Workspace.Normativity.Contrib.WarrantSolvency.Schema.bounded_iff_frequency` (theorem) in lean/Workspace/Normativity/Contrib/WarrantSolvency.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (S : Schema) (B : ℝ) :
        (∀ n, -B ≤ liability S.realized S.held n) ↔
          ∀ n, S.c * S.undefeatedCount n - S.trueCount n ≤ B
