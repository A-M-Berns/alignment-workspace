---
id: rows.incompatibility-entailment
kind: and
children: [rows.incompatibility-entailment.record, rows.incompatibility-entailment.bridge, rows.incompatibility-entailment.complete]
work: [{kind: round, ref: projects/normativity/rounds/2026-11-08-content-recollection}, {kind: priorities, ref: 118}, {kind: decision, ref: 2026-11-08--content-is-role-among-rows-expresses-demands-no-more}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
For every list of rational rows and every row, the list incompatibility-entails the row — every list incompatible with the row is incompatible with the list — exactly when the row is a nonnegative combination, with slack, of the list's rows and the cube rows.

## Source
projects/normativity/CLAIMS.md, entry `rows.incompatibility-entailment` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 118).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.IncompatibilitySemantics.incEntails_iff_certEntails` in lean/Workspace/Normativity/Contrib/IncompatibilitySemantics.lean.

## Notes
Filed by the content-recollection round (prompts/2026-11-08-content-recollection) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. The registry's `answers_item` is the `priorities` pointer to item 118 (ruling F2).
