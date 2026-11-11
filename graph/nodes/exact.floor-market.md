---
id: exact.floor-market
kind: and
children: [exact.floor-market.record, exact.floor-market.bridge, exact.floor-market.complete]
work: [{kind: round, ref: projects/normativity/rounds/2026-11-10-exact-conditions-capital}, {kind: priorities, ref: 136}, {kind: decision, ref: 2026-11-10--exact-conditions-as-dual-certified-interface}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@claude-fable-5-2"
---
## Statement
Every assessment and every schedule of one floor per day has a dual-certified market: prices satisfying each floor exactly, with ceiling 3.

## Source
projects/normativity/CLAIMS.md, entry `exact.floor-market` (class lean-proved, status active, origin round 2026-11-10-exact-conditions-capital; answers item 136).
Documentation: verification: projects/normativity/rounds/2026-11-10-exact-conditions-capital/THEOREM.md; context: projects/normativity/rounds/2026-11-10-exact-conditions-capital/REPORT.md.
The signature of `Workspace.Normativity.Contrib.ExactConditions.FloorSchedule.exists_market` in lean/Workspace/Normativity/Contrib/ExactConditionsFloor.lean.

## Notes
Filed by the exact-conditions round (prompts/2026-11-10-exact-conditions-capital) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. The registry's `answers_item` is the `priorities` pointer to item 136 (ruling F2).
