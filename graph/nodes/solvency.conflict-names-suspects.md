---
id: solvency.conflict-names-suspects
kind: and
children: [solvency.conflict-names-suspects.record, solvency.conflict-names-suspects.bridge, solvency.conflict-names-suspects.complete]
work: [{kind: round, ref: projects/normativity/rounds/2026-11-07-score-side-binding}, {kind: priorities, ref: 133}, {kind: decision, ref: 2026-11-07--conduct-binds-on-score-warrants-on-prices}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
Against a bundle, a Farkas certificate over the bundle's allowed rows has, at every point of the cube, a positively weighted row of the bundle itself that is violated there; so if every held row is valid at a point no such certificate exists, and a conflict names a mis-admission among the rows it weights.

## Source
projects/normativity/CLAIMS.md, entry `solvency.conflict-names-suspects` (class lean-proved, status active, origin round 2026-11-07-score-side-binding; answers item 133).
Documentation: verification: projects/normativity/rounds/2026-11-07-score-side-binding/THEOREM.md; context: projects/normativity/rounds/2026-11-07-score-side-binding/REPORT.md.
The signature of `Workspace.Normativity.Contrib.WarrantSolvency.suspect_in_bundle` in lean/Workspace/Normativity/Contrib/WarrantSolvency.lean.

## Notes
Filed by the score-side-binding round (prompts/2026-11-07-score-side-binding) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. The registry's `answers_item` is the `priorities` pointer to item 133 (ruling F2).
