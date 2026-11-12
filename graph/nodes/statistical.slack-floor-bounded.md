---
id: statistical.slack-floor-bounded
kind: and
children: [statistical.slack-floor-bounded.record, statistical.slack-floor-bounded.bridge, statistical.slack-floor-bounded.complete]
work: [{kind: round, ref: projects/normativity/rounds/2026-11-12-statistical-conditions}, {kind: priorities, ref: 138}, {kind: decision, ref: 2026-11-12--statistical-floor-as-threshold-dichotomy}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@claude-fable-5-2"
---
## Statement
A floor whose prices clear it by a margin δ from some day on costs an account bounded below by c(ε/δ + the multipliers of the earlier days).

## Source
projects/normativity/CLAIMS.md, entry `statistical.slack-floor-bounded` (class lean-proved, status active, origin round 2026-11-12-statistical-conditions; answers item 138).
Documentation: verification: projects/normativity/rounds/2026-11-12-statistical-conditions/THEOREM.md; context: projects/normativity/rounds/2026-11-12-statistical-conditions/REPORT.md.
The signature of `Workspace.Normativity.Contrib.StatisticalConditions.DualCertifiedMarket.accountBounded_of_eventually_slack` in lean/Workspace/Normativity/Contrib/StatisticalConditions.lean.

## Notes
Filed by the statistical-conditions round (prompts/2026-11-12-statistical-conditions) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. The registry's `answers_item` is the `priorities` pointer to item 138 (ruling F2).
