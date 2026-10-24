---
id: item-62
kind: leaf
leaf_kind: task
action: "Execute item 62 per its deliverable shape and acceptance check: The inertness dichotomy in Lean."
who: agent
item: "62"
title: "The inertness dichotomy in Lean"
section: "Normativity line — legitimacy"
maintainer_order: 38
difficulty: "entry"
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`lean-proved` — one theorem in a contribution namespace, with an inhabitation witness."
acceptance: "the `lean` job, and `#print axioms` clean."
context: ["projects/normativity/legitimacy/rounds/2026-08-25-end-to-end-vertical-slice/VERTICAL_SLICE.md"]
author: "@smithy-verity"
size: M
size_reason: "one item entry of 133 words"
version: 1
---
## Statement
Item 62, The inertness dichotomy in Lean, is delivered in the shape its entry states: `lean-proved` — one theorem in a contribution namespace, with an inhabitation witness.

## Source
PRIORITIES.md, item 62 (The inertness dichotomy in Lean); its context: `projects/normativity/legitimacy/rounds/2026-08-25-end-to-end-vertical-slice/VERTICAL_SLICE.md` §11 (T2); `lean/Workspace/Normativity/Contrib/{ConstraintSchedule,DeductiveRegion}.lean`.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
The dichotomy is three lines and uses only convexity: if every stage-consistent
world satisfies a finite system of half-space rows, then the convex hull of those
worlds lies inside the region the rows cut, so the intersection is the hull.
Stated over the repository's own objects it says
`ConstraintSchedule`'s `hadm` implies `regionPred` contains
`DeductiveRegion`'s hull, hence that the enforced region equals the deductive one.

It is currently a paper derivation checked on finite instances, and it is the
premise item 61 exists to answer.

*Deliverable shape:* `lean-proved` — one theorem in a contribution namespace, with
an inhabitation witness.
*Acceptance check:* the `lean` job, and `#print axioms` clean.
*Context:*
`projects/normativity/legitimacy/rounds/2026-08-25-end-to-end-vertical-slice/VERTICAL_SLICE.md`
§11 (T2); `lean/Workspace/Normativity/Contrib/{ConstraintSchedule,DeductiveRegion}.lean`.
*Consumed by:* item 61, which needs the dichotomy to be a statement of record
before its own negative half means anything.
