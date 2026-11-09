---
id: precedent.rationalizable-iff-acyclic
kind: and
children: [precedent.rationalizable-iff-acyclic.record, precedent.rationalizable-iff-acyclic.bridge, precedent.rationalizable-iff-acyclic.complete]
work: [{kind: round, ref: projects/normativity/rounds/2026-11-08-content-recollection}, {kind: priorities, ref: 117}, {kind: decision, ref: 2026-11-08--precedent-read-off-record-constrains-docket}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
A base of decided cases — each the reasons that prevailed and the reasons that were outweighed — is rationalized by one strict order among reason sets, irreflexive and transitive, exactly when the graph on its cases, with an edge from a case to each case whose prevailing reasons its outweighed reasons cover, has no cycle.

## Source
projects/normativity/CLAIMS.md, entry `precedent.rationalizable-iff-acyclic` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 117).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.PrecedentConstraint.rationalizable_iff_acyclic` in lean/Workspace/Normativity/Contrib/PrecedentConstraint.lean.

## Notes
Filed by the content-recollection round (prompts/2026-11-08-content-recollection) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. The registry's `answers_item` is the `priorities` pointer to item 117 (ruling F2).
