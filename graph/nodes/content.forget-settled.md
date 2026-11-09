---
id: content.forget-settled
kind: and
children: [content.forget-settled.record, content.forget-settled.bridge, content.forget-settled.complete]
work: [{kind: round, ref: projects/normativity/rounds/2026-11-08-content-recollection}, {kind: priorities, ref: 134}, {kind: decision, ref: 2026-11-09--forgetting-is-projection-settled-safe-live-not}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
Once a coordinate is settled it may be forgotten at no cost: the seed's rows specialized at that settlement and restricted to the other coordinates determine the projection of the forced region onto those coordinates under every docket state and every later settlement.

## Source
projects/normativity/CLAIMS.md, entry `content.forget-settled` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 134).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.Forgetting.forget_settled` in lean/Workspace/Normativity/Contrib/Forgetting.lean.

## Notes
Filed by the content-recollection round's follow-up (prompts/2026-11-08-content-recollection, PROMPT-followup.md) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. The registry's `answers_item` is the `priorities` pointer to item 134 (ruling F2).
