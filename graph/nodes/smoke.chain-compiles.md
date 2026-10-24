---
id: smoke.chain-compiles
kind: and
children: [smoke.chain-compiles.record, smoke.chain-compiles.bridge, smoke.chain-compiles.complete]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
work: [{kind: round, ref: prompts/2026-08-10-repo-scaffolding}, {kind: decision, ref: 2026-08-11--setup-scrub-reports-removed-root}, {kind: priorities, ref: 13}]
author: "@smithy-verity"
---
## Statement
States a Mathlib limit in the dependency's own vocabulary, so it typechecks only if both halves of the chain agree.

## Source
projects/normativity/CLAIMS.md, entry `smoke.chain-compiles` (class lean-proved, status active, origin round 2026-08-10-repo-scaffolding; answers item 13).
Documentation: verification: prompts/2026-08-10-repo-scaffolding/REPORT.md; context: README.md.
The signature of `Workspace.Smoke.chain_compiles` in lean/Workspace/Smoke.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. Registry note: States a Mathlib limit in the dependency's own vocabulary, so it typechecks only if both halves of the chain agree. The registry's `answers_item` is the `priorities` pointer to item 13 (ruling F2).
