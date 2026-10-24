---
id: compiler.deductive-end-to-end
kind: and
children: [compiler.deductive-end-to-end.record, compiler.deductive-end-to-end.bridge, compiler.deductive-end-to-end.complete, compiler.deductive-end-to-end.h-fragment-schedule, compiler.deductive-end-to-end.h-tolerance-schedule, compiler.deductive-end-to-end.h-process-certificate, compiler.deductive-end-to-end.h-stages-satisfiable]
work: [{kind: round, ref: projects/normativity/rounds/2026-08-18-projection-enforcement}, {kind: priorities, ref: 48}, {kind: round, ref: projects/enabling/rounds/2026-10-24-site-vertical-slice}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
The source's criterion over D together with per-date conformance at a computable tolerance schedule, assuming nothing about the deductive process beyond the source's own certificate plus propositional satisfiability of each stage. Computable, not efficient: the generator is doubly exponential in the fragment dimension.

## Source
projects/normativity/CLAIMS.md, entry `compiler.deductive-end-to-end` (class lean-proved, status active, origin round 2026-08-18-projection-enforcement; answers item 48).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-18-projection-enforcement/FINAL_FORMALIZATION_STATUS.md.
The signature of `Workspace.Normativity.Contrib.DeductiveEffective.deductive_end_to_end` in lean/Workspace/Normativity/Contrib/DeductiveEffective.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature. The site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice) connected it by reading: its hypotheses are the four leaves (two schedules, the source's certificate, satisfiable stages), its bridge names the gap between the claim and the declaration, and it is a conjunct of the informal claim traderized-finite-date-conformance, a shared-claim root of operative-force, rather than a node that frame holds. Registry note: The source's criterion over D together with per-date conformance at a computable tolerance schedule, assuming nothing about the deductive process beyond the source's own certificate plus propositional satisfiability of each stage. Computable, not efficient: the generator is doubly exponential in the fragment dimension. The registry's `answers_item` is the `priorities` pointer to item 48 (ruling F2).
