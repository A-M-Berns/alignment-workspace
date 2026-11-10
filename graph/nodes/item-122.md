---
id: item-122
kind: leaf
leaf_kind: task
action: "Execute item 122 per its deliverable shape and acceptance check: The transport's negated-form drop."
who: agent
item: "122"
title: "The transport's negated-form drop"
section: "Deference line — second wave"
maintainer_order: 115
difficulty: "entry"
heading_notes: " — *narrowed 2026-11-08: the Lean half is landed in a general form — `Conservativity.pull` along `Translation.ofMap ρ` is the branch's `transport ρ`, exact on rows (`pull_ofMap_sat_iff`), and `mapForm` relabels the three leverage forms; the fixture code's negated-form drop and the convergence round's pull-back fixtures remain*"
project: normativity.seed
dispatchable: true
item_status: open
deliverable: "the fix, the landed section, green fixtures."
acceptance: "`python3 tests/run.py` green in both seed rounds; Lean green."
context: ["projects/normativity/seed/rounds/2026-09-16-seed-statics/src/seed.py", "projects/normativity/seed/rounds/2026-09-17-convergence-measure/REPORT.md"]
work:
  - {kind: decision, ref: 2026-10-22--survivors-grounded-fixed-point-defeaters-shared}
  - {kind: round, ref: projects/normativity/rounds/2026-11-08-content-recollection}
  - {kind: decision, ref: 2026-11-08--vocabulary-change-is-translation-conservativity-criterion}
author: "@smithy-verity"
size: S
size_reason: "one item entry of 104 words"
version: 1
---
## Statement
Item 122, The transport's negated-form drop, is delivered in the shape its entry states: the fix, the landed section, green fixtures.

## Source
ATTENTION.md, item 122 (The transport's negated-form drop); its context: `projects/normativity/seed/rounds/2026-09-17-convergence-measure/REPORT.md`; `projects/normativity/seed/rounds/2026-09-16-seed-statics/src/seed.py`.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into ATTENTION.md by checkers/attention_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
The seed-statics branch's `transport_seed` (its `src/seed.py`, cited by the convergence
round's `REPORT.md` §3 of *What is not shown*) carries every form as a plain `Form` and drops
the negated forms its own fixtures use; the Lean `transport`/`transport_sat_iff` (branch §9)
is exact on rows but was not landed (`projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/LANDING.md`). A known defect, filed and not
fixed by the landing round. Wanted: transport of negated forms in the fixture code, the Lean
§9 landed with it, and the convergence round's pull-back fixtures re-run.

*Deliverable shape:* the fix, the landed section, green fixtures.
*Acceptance check:* `python3 tests/run.py` green in both seed rounds; Lean green.
*Context:* `projects/normativity/seed/rounds/2026-09-17-convergence-measure/REPORT.md`;
`projects/normativity/seed/rounds/2026-09-16-seed-statics/src/seed.py`.
