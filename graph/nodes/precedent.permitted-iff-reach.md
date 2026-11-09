---
id: precedent.permitted-iff-reach
kind: and
children: [precedent.permitted-iff-reach.record, precedent.permitted-iff-reach.bridge, precedent.permitted-iff-reach.complete]
work: [{kind: round, ref: projects/normativity/rounds/2026-11-08-content-recollection}, {kind: priorities, ref: 117}, {kind: decision, ref: 2026-11-09--holding-is-what-permission-reads-assessor-sets-case}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
A continuation is permitted by a base of decided cases exactly when the base is rationalizable and its reach — one reason set covering another, or standing above it in the transitive closure of the cases' decisions — does not put the reasons the continuation outweighs at or above the reasons it lets prevail.

## Source
projects/normativity/CLAIMS.md, entry `precedent.permitted-iff-reach` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 117).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.PrecedentHolding.permitted_iff` in lean/Workspace/Normativity/Contrib/PrecedentHolding.lean.

## Notes
Filed by the content-recollection round's follow-up (prompts/2026-11-08-content-recollection, PROMPT-followup.md) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. The registry's `answers_item` is the `priorities` pointer to item 117 (ruling F2).
