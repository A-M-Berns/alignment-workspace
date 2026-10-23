---
id: force.deductive-cumulative-nonneg
kind: and
children: [force.deductive-cumulative-nonneg.record, force.deductive-cumulative-nonneg.bridge, force.deductive-cumulative-nonneg.complete]
work: [{kind: round, ref: projects/normativity/rounds/2026-08-16-traderized-enforcement}, {kind: priorities, ref: 41}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
Per-date nonnegativity summed. This is why deduction is the free case rather than one instance among equals: the risk capital is exactly zero, so no affordability side-condition binds and the tolerance schedule is unconstrained.

## Source
projects/normativity/CLAIMS.md, entry `force.deductive-cumulative-nonneg` (class lean-proved, status active, origin round 2026-08-16-traderized-enforcement; answers item 41).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-16-traderized-enforcement/DEDUCTION_SPECIAL_CASE.md.
The signature of `Workspace.Normativity.Contrib.DeductiveEnforcement.enforcement_netWorth_nonneg` in lean/Workspace/Normativity/Contrib/DeductiveEnforcement.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. Registry note: Per-date nonnegativity summed. This is why deduction is the free case rather than one instance among equals: the risk capital is exactly zero, so no affordability side-condition binds and the tolerance schedule is unconstrained. The registry's `answers_item` is the `priorities` pointer to item 41 (ruling F2).
