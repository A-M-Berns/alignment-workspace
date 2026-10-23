---
id: maxmin.representation
kind: and
children: [maxmin.representation.record, maxmin.representation.bridge, maxmin.representation.complete]
work: [{kind: round, ref: projects/normativity/rounds/2026-08-18-maxmin-representation}, {kind: priorities, ref: 50}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
Ovchinnikov Theorem 4.1(a), for a nonempty convex domain in a topological real vector space. The source's proof silently needs full-dimensionality; the statement does not, and the round's errata carry a counterexample to the source's own nonemptiness claim.

## Source
projects/normativity/CLAIMS.md, entry `maxmin.representation` (class lean-proved, status active, origin round 2026-08-18-maxmin-representation; answers item 50).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-18-maxmin-representation/README.md.
The signature of `Workspace.Normativity.Contrib.MaxMinRepresentation.exists_maxMin_representation` in lean/Workspace/Normativity/Contrib/MaxMinRepresentation.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. Registry note: Ovchinnikov Theorem 4.1(a), for a nonempty convex domain in a topological real vector space. The source's proof silently needs full-dimensionality; the statement does not, and the round's errata carry a counterexample to the source's own nonemptiness claim. The registry's `answers_item` is the `priorities` pointer to item 50 (ruling F2).
