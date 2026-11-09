---
id: memory.live-forget-cost
kind: and
children: [memory.live-forget-cost.record, memory.live-forget-cost.bridge, memory.live-forget-cost.complete]
work: [{kind: round, ref: projects/normativity/rounds/2026-11-08-content-recollection}, {kind: priorities, ref: 135}, {kind: decision, ref: 2026-11-09--forgetting-is-projection-settled-safe-live-not}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
Forgetting a coordinate that is still unsettled costs the response to its later settlement: over the one commitment P(Y) ≥ 3/4 · P(X), forgetting X before it settles leaves no constraint on P(Y), while the full record forces P(Y) into [3/4, 1] once X settles true, and forgetting X after it has settled keeps P(Y) ≥ 3/4.

## Source
projects/normativity/CLAIMS.md, entry `memory.live-forget-cost` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 135).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.Forgetting.live_forget_cost` in lean/Workspace/Normativity/Contrib/Forgetting.lean.

## Notes
Filed by the content-recollection round's follow-up (prompts/2026-11-08-content-recollection, PROMPT-followup.md) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. The registry's `answers_item` is the `priorities` pointer to item 135 (ruling F2).
