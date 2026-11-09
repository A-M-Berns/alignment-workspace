---
id: seed.adapter-certificates-exist
kind: and
children: [seed.adapter-certificates-exist.record, seed.adapter-certificates-exist.bridge, seed.adapter-certificates-exist.complete]
work: [{kind: round, ref: projects/normativity/rounds/2026-11-08-content-recollection}, {kind: priorities, ref: 118}, {kind: decision, ref: 2026-11-08--content-is-role-among-rows-expresses-demands-no-more}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
Every valid upper bound on a rational linear functional over a bundle's region is certified: some functional certificate whose positively weighted rows are admitted into the bundle under their citations has value at most the bound.

## Source
projects/normativity/CLAIMS.md, entry `seed.adapter-certificates-exist` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 118).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.AdapterCertificates.exists_citedFunctional` in lean/Workspace/Normativity/Contrib/AdapterCertificates.lean.

## Notes
Filed by the content-recollection round's follow-up (prompts/2026-11-08-content-recollection, PROMPT-followup.md) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. The registry's `answers_item` is the `priorities` pointer to item 118 (ruling F2).
