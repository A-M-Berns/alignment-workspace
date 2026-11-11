---
id: exact.prefix-reserve-bound
kind: and
children: [exact.prefix-reserve-bound.record, exact.prefix-reserve-bound.bridge, exact.prefix-reserve-bound.complete]
work: [{kind: round, ref: projects/normativity/rounds/2026-11-10-exact-conditions-capital}, {kind: priorities, ref: 137}, {kind: decision, ref: 2026-11-10--exact-conditions-as-dual-certified-interface}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@claude-fable-5-2"
---
## Statement
A prefix reserve bounds the account below by −U(1 − r)/r at every profile it retains mass r on.

## Source
projects/normativity/CLAIMS.md, entry `exact.prefix-reserve-bound` (class lean-proved, status active, origin round 2026-11-10-exact-conditions-capital; answers item 137).
Documentation: verification: projects/normativity/rounds/2026-11-10-exact-conditions-capital/THEOREM.md; context: projects/normativity/rounds/2026-11-10-exact-conditions-capital/REPORT.md.
The signature of `Workspace.Normativity.Contrib.ExactConditions.DualCertifiedMarket.reserve_bound` in lean/Workspace/Normativity/Contrib/ExactConditionsReserve.lean.

## Notes
Filed by the exact-conditions round (prompts/2026-11-10-exact-conditions-capital) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. The registry's `answers_item` is the `priorities` pointer to item 137 (ruling F2).
