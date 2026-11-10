---
id: memory.selective-forgetting
kind: and
children: [memory.selective-forgetting.record, memory.selective-forgetting.bridge, memory.selective-forgetting.complete]
work: [{kind: round, ref: projects/normativity/rounds/2026-11-08-content-recollection}, {kind: priorities, ref: 135}, {kind: decision, ref: 2026-11-09--forgetting-is-projection-settled-safe-live-not}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
Choosing what to forget after seeing the record obtains what no choice fixed in advance does: over two records whose one obligation on φ runs through A in the first and through B in the second, dropping the coordinate the obligation runs through leaves φ the interval [0, 1] on both once A and B settle true, each coordinate fixed in advance leaves [3/4, 1] on one of them, and the full record forces [3/4, 1] on both.

## Source
projects/normativity/CLAIMS.md, entry `memory.selective-forgetting` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 135).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.Forgetting.selective_forgetting` in lean/Workspace/Normativity/Contrib/Forgetting.lean.

## Notes
Filed by the content-recollection round's follow-up (prompts/2026-11-08-content-recollection, PROMPT-followup.md) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. The registry's `answers_item` is the `priorities` pointer to item 135 (ruling F2).
