---
id: memory.schedule-slack
kind: and
children: [memory.schedule-slack.record, memory.schedule-slack.bridge, memory.schedule-slack.complete]
work: [{kind: round, ref: projects/normativity/rounds/2026-11-08-content-recollection}, {kind: priorities, ref: 135}, {kind: decision, ref: 2026-11-09--forgetting-is-projection-settled-safe-live-not}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
Forgetting with loss composes as slack: along a schedule of forgetting steps, each agreeing with an exact step except on a set of worlds, the excess of a row at the credence held at any stage is at most its excess under the exact schedule plus the row's oscillation times the sum, over the earlier stages, of the mass the held credence placed on that stage's set.

## Source
projects/normativity/CLAIMS.md, entry `memory.schedule-slack` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 135).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.Forgetting.schedule_slack` in lean/Workspace/Normativity/Contrib/Forgetting.lean.

## Notes
Filed by the content-recollection round's follow-up (prompts/2026-11-08-content-recollection, PROMPT-followup.md) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. The registry's `answers_item` is the `priorities` pointer to item 135 (ruling F2).
