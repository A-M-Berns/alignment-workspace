---
id: item-108
kind: leaf
leaf_kind: question
action: "Execute PRIORITIES item 108: state correct, sufficient and value for valuations with no outside fact, prove that the thick conditions deliver them or state the obstruction, and write the note linking the item to the inferentialist (no-territory) case of Stage 3."
who: agent
files: [lean/, projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/]
item: "108"
title: "The thin specification for evaluations, where no outside fact plays the world's role"
section: "Deference line — second wave"
maintainer_order: 101
difficulty: "open"
project: deference
dispatchable: true
item_status: open
deliverable: "Lean in a contribution namespace, in the style of `ThinLegitimacy.lean`; an exact fixture."
acceptance: "`python3 tests/run.py` green; Lean audits clean."
context: ["projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md"]
author: "@smithy-verity"
size: L
size_reason: "one item with a new satisfaction theorem"
version: 1
---
## Statement
The thin properties have a form for valuations with no outside fact to be
correct about, and the thick conditions deliver them.

## Source
PRIORITIES.md, item 108 ("The thin specification for evaluations, where no
outside fact plays the world's role"): candidates for correct, sufficient and
value for a valuation, and the theorem that the thick conditions deliver them.

## Notes
This is the case with no territory, the inferentialist case of the syntax frame
(the filing session's reading); the definition crux's third picture is about
it.

## Item
Part A of the thin-legitimacy round states *correct*, *sufficient* and *value* over a
finite set of worlds with her prior: the credence is about a fact, and *correct* compares
it with the actual conditional.  Her evaluations — what the fidelity score reads — have no
outside fact to be correct about.  Wanted: the same two-level structure for evaluations:
what the thin properties become when the object of her later judgment is a valuation rather
than a credence (candidates: *correct* as agreement with the valuation her program yields
on the actual record; *sufficient* unchanged; *value* as a decision-theoretic statement
about acting on the valuation), and the theorem that the thick conditions deliver them.

*Deliverable shape:* Lean in a contribution namespace, in the style of
`ThinLegitimacy.lean`; an exact fixture.
*Acceptance check:* `python3 tests/run.py` green; Lean audits clean.
*Context:* `projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md` Part A; the fidelity
score's evaluator (`Headline.evaluation`); the after-compromise band.
*Consumed by:* the round that restates the segment gate's "counts" on the thin level, so
that the post's "illegitimate futures count as bad" has a thin-level reading.
*A solution ships:* the three properties for evaluations with the satisfaction theorem, or
the obstruction.
