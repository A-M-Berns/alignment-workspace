---
id: force.deductive-day-nonneg
kind: and
children: [force.deductive-day-nonneg.record, force.deductive-day-nonneg.bridge, force.deductive-day-nonneg.complete]
work: [{kind: round, ref: projects/normativity/rounds/2026-08-16-traderized-enforcement}, {kind: priorities, ref: 41}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
Every deductively plausible world lies in the coherence polytope, so the enforcement position's day value is nonnegative there for any nonnegative intensity.

## Source
projects/normativity/CLAIMS.md, entry `force.deductive-day-nonneg` (class lean-proved, status active, origin round 2026-08-16-traderized-enforcement; answers item 41).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-16-traderized-enforcement/DEDUCTION_SPECIAL_CASE.md.
The signature of `Workspace.Normativity.Contrib.DeductiveEnforcement.enforcement_day_value_nonneg` in lean/Workspace/Normativity/Contrib/DeductiveEnforcement.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. Registry note: Every deductively plausible world lies in the coherence polytope, so the enforcement position's day value is nonnegative there for any nonnegative intensity. The registry's `answers_item` is the `priorities` pointer to item 41 (ruling F2).
