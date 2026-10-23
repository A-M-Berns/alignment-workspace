---
id: force.strategy-value
kind: and
children: [force.strategy-value.record, force.strategy-value.bridge, force.strategy-value.complete]
work: [{kind: round, ref: projects/normativity/rounds/2026-08-16-traderized-enforcement}, {kind: priorities, ref: 41}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
The compiled enforcement position is a legal Strategy whose value against a payout table is exactly the quantity the force inequalities bound. Without this identity those inequalities are algebra about a vector rather than theorems about the strategy the market prices.

## Source
projects/normativity/CLAIMS.md, entry `force.strategy-value` (class lean-proved, status active, origin round 2026-08-16-traderized-enforcement; answers item 41).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-16-traderized-enforcement/ENFORCEMENT.md.
The signature of `Workspace.Normativity.Contrib.EnforcementStrategy.marketValueRat_enforcementStrategy` in lean/Workspace/Normativity/Contrib/EnforcementStrategy.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. Registry note: The compiled enforcement position is a legal Strategy whose value against a payout table is exactly the quantity the force inequalities bound. Without this identity those inequalities are algebra about a vector rather than theorems about the strategy the market prices. The registry's `answers_item` is the `priorities` pointer to item 41 (ruling F2).
