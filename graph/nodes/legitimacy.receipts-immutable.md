---
id: legitimacy.receipts-immutable
kind: and
children: [legitimacy.receipts-immutable.record, legitimacy.receipts-immutable.bridge, legitimacy.receipts-immutable.complete]
superseded_by: integrity.receipts-immutable
work: [{kind: round, ref: projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation}, {kind: priorities, ref: 78}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
Substitution at live ports keeps every terminal receipt and adds only the terminals of the substituted accounts. With `livePorts_subst` this is the three-fate accounting at the leaf level: terminal fates persist, live leaves are replaced.

## Source
projects/normativity/CLAIMS.md, entry `legitimacy.receipts-immutable` (class lean-proved, status superseded, origin round 2026-09-06-mathematical-consolidation; answers item 78).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/THEOREMS.md; context: projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/CONSOLIDATION.md.
The signature of `Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.terminals_subst` in lean/Workspace/Normativity/Contrib/OccurrenceIntegrity.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. Registry note: Substitution at live ports keeps every terminal receipt and adds only the terminals of the substituted accounts. With `livePorts_subst` this is the three-fate accounting at the leaf level: terminal fates persist, live leaves are replaced. Superseded 2026-09-25 by `integrity.receipts-immutable`; the declaration name is kept resolving by a deprecated alias for one release. The registry's `answers_item` is the `priorities` pointer to item 78 (ruling F2).
