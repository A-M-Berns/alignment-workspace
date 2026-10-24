---
id: item-129
kind: leaf
leaf_kind: route
given: traderized-finite-date-conformance@valid
action: "Test whether the normativity line's constraint compiler can enforce a per-day gap-bet bound (the novice's expectation of each signed gap bet at least minus a schedule) while preserving the criterion, and state the obstruction if not."
who: agent
item: "129"
title: "A per-day gap-bet bound from the constraint compiler"
section: "Normativity line — traderized enforcement"
maintainer_order: 138
difficulty: "substantial"
heading_notes: ""
project: normativity
dispatchable: true
item_status: open
deliverable: "a theorem that the compiled enforcer's per-day gap bets are bounded below by a schedule while the criterion is preserved, or the stated obstruction."
acceptance: "Lean green; the bound or the obstruction stated against the conformance clause of `deductive_end_to_end`."
context: ["projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md", "projects/normativity/rounds/2026-08-16-traderized-enforcement/PROOF_CLOSURE.md"]
author: "@smithy-verity"
size: S
size_reason: "one route of the improvement claim"
version: 1
---
## Statement
The compiled enforcer's per-day gap bets are bounded below by a schedule while the criterion is preserved, so that the conformance the compiler gives is a trust bound the deference line can read.

## Source
projects/normativity/rounds/2026-08-16-traderized-enforcement/PROOF_CLOSURE.md; projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; the step's earlier action, filed as this round's item 129.
A route of the improvement claim on traderized-finite-date-conformance, filed by reading by the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice).

## Notes
Filed by the site-vertical-slice round as the route of the improvement claim that the step's earlier action asked for; the entry's text is the Item section below, rendered into PRIORITIES.md by checkers/priorities_render.py.

## Item
The traderization arc compiles a constraint on prices into a legal trading strategy and, for
deduction, gives per-date conformance within a tolerance schedule while preserving the
criterion (`compiler.deductive-end-to-end`). The deference line reads conformance as a
trust bound only if it bounds the novice's gap bets day by day. Wanted: whether the
constraint compiler can enforce a per-day gap-bet bound, the novice's expectation of each
signed gap bet at least minus a schedule, while preserving the criterion; and, if not, the
obstruction stated against the conformance clause.

*Deliverable shape:* a theorem that the compiled enforcer's per-day gap bets are bounded
below by a schedule while the criterion is preserved, or the stated obstruction.
*Acceptance check:* Lean green; the bound or the obstruction stated against the conformance
clause of `deductive_end_to_end`.
*Context:* `projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md`;
`projects/normativity/rounds/2026-08-16-traderized-enforcement/PROOF_CLOSURE.md`; the step
`traderized-finite-date-conformance` of the map, whose action this item was.
