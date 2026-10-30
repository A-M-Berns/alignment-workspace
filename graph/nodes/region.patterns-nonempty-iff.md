---
id: region.patterns-nonempty-iff
kind: and
children: [region.patterns-nonempty-iff.record, region.patterns-nonempty-iff.bridge, region.patterns-nonempty-iff.complete]
work: [{kind: round, ref: projects/normativity/rounds/2026-08-19-deductive-region}, {kind: priorities, ref: 51}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
A biconditional, so the satisfiability hypothesis is exact rather than merely sufficient: no weaker hypothesis suffices and no stronger one is used.

## Source
projects/normativity/CLAIMS.md, entry `region.patterns-nonempty-iff` (class lean-proved, status active, origin round 2026-08-19-deductive-region; answers item 51).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: prompts/2026-08-19-deductive-region/REPORT.md.
The signature of `Workspace.Normativity.Contrib.DeductiveRegion.admissiblePatterns_ne_nil_iff` in lean/Workspace/Normativity/Contrib/DeductiveRegion.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. Registry note: A biconditional, so the satisfiability hypothesis is exact rather than merely sufficient: no weaker hypothesis suffices and no stronger one is used. The registry's `answers_item` is the `priorities` pointer to item 51 (ruling F2).
