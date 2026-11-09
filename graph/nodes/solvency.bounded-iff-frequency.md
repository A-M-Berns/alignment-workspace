---
id: solvency.bounded-iff-frequency
kind: and
children: [solvency.bounded-iff-frequency.record, solvency.bounded-iff-frequency.bridge, solvency.bounded-iff-frequency.complete]
work: [{kind: round, ref: projects/normativity/rounds/2026-11-07-score-side-binding}, {kind: priorities, ref: 61}, {kind: decision, ref: 2026-11-07--conduct-binds-on-score-warrants-on-prices}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
For a warrant schema with timely-settling instances, the enforcer's cumulative liability (the settled consequent against the held strength, one unit per undefeated instance) is bounded below by −B at every date iff c·U_n − T_n ≤ B at every date, U_n the undefeated count and T_n the true consequents among them; an instance of the deference identity bounded_iff_not_outperformed.

## Source
projects/normativity/CLAIMS.md, entry `solvency.bounded-iff-frequency` (class lean-proved, status active, origin round 2026-11-07-score-side-binding; answers item 61).
Documentation: verification: projects/normativity/rounds/2026-11-07-score-side-binding/THEOREM.md; context: projects/normativity/rounds/2026-11-07-score-side-binding/REPORT.md.
The signature of `Workspace.Normativity.Contrib.WarrantSolvency.Schema.bounded_iff_frequency` in lean/Workspace/Normativity/Contrib/WarrantSolvency.lean.

## Notes
Filed by the score-side-binding round (prompts/2026-11-07-score-side-binding) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. The registry's `answers_item` is the `priorities` pointer to item 61 (ruling F2).
