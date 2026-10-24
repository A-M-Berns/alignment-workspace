---
id: magnitude.sq-error-split.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.MagnitudePrediction.sq_error_split
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: magnitude.sq-error-split
---
## Statement
The declaration Workspace.Deference.Contrib.MagnitudePrediction.sq_error_split is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `magnitude.sq-error-split` (class lean-proved, status active, origin round 2026-08-11-phase-ii-prediction; answers item 21).
Documentation: verification: prompts/2026-08-11-phase-ii-prediction/REPORT.md; context: prompts/2026-08-11-phase-ii-prediction/REPORT.md.
The signature of `Workspace.Deference.Contrib.MagnitudePrediction.sq_error_split` (theorem) in lean/Workspace/Deference/Contrib/MagnitudePrediction.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (y p : ℝ) (hy : y * y = y) :
        (y - p) ^ 2 = (1 - 2 * p) * (y - p) + p * (1 - p)
