---
id: deconfusing.theorem3a
kind: and
children: [deconfusing.theorem3a.record, deconfusing.theorem3a.bridge, deconfusing.theorem3a.complete]
work: [{kind: round, ref: prompts/2026-10-17-post-companion-formalization}, {kind: priorities, ref: 107}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
Unbiasedness From Feedback is the named hypothesis `Sequential.UnbiasedFromFeedback`, assumed rather than derived (PRIORITIES item 111). limsup in the eventual form `LimsupLE`.

## Source
projects/deference/CLAIMS.md, entry `deconfusing.theorem3a` (class lean-proved, status active, origin round 2026-10-17-post-companion-formalization; answers item 107).
Documentation: verification: prompts/2026-10-17-post-companion-formalization/REPORT.md; context: prompts/2026-10-17-post-companion-formalization/PROMPT.md; companion: wiki/Deconfusing-Corrigibility-Companion.md.
The signature of `Workspace.Deference.Contrib.DeconfusingCorrigibility.Sequential.theorem3a` in lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. Registry note: Unbiasedness From Feedback is the named hypothesis `Sequential.UnbiasedFromFeedback`, assumed rather than derived (PRIORITIES item 111). limsup in the eventual form `LimsupLE`. Inhabited by `Witness.theorem3_instance` on `Witness.sequential` (estimates equal to realized scores). The registry's `answers_item` is the `priorities` pointer to item 107 (ruling F2).
