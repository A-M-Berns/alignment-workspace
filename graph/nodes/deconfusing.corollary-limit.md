---
id: deconfusing.corollary-limit
kind: and
children: [deconfusing.corollary-limit.record, deconfusing.corollary-limit.bridge, deconfusing.corollary-limit.complete]
work: [{kind: round, ref: prompts/2026-10-17-post-companion-formalization}, {kind: priorities, ref: 107}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
ε_K → 0 in the eventual form `LimsupLE X.ε 0`. Inhabited by `Witness.corollary_instance` (`Witness.exploration_ε_limsup`).

## Source
projects/deference/CLAIMS.md, entry `deconfusing.corollary-limit` (class lean-proved, status active, origin round 2026-10-17-post-companion-formalization; answers item 107).
Documentation: verification: prompts/2026-10-17-post-companion-formalization/REPORT.md; context: prompts/2026-10-17-post-companion-formalization/PROMPT.md; companion: wiki/Deconfusing-Corrigibility-Companion.md.
The signature of `Workspace.Deference.Contrib.DeconfusingCorrigibility.Exploration.corollary_limit` in lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. Registry note: ε_K → 0 in the eventual form `LimsupLE X.ε 0`. Inhabited by `Witness.corollary_instance` (`Witness.exploration_ε_limsup`). The registry's `answers_item` is the `priorities` pointer to item 107 (ruling F2).
