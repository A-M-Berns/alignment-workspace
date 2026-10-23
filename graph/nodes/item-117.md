---
id: item-117
kind: leaf
leaf_kind: task
action: "Execute item 117 per its deliverable shape and acceptance check: The selection lock: a canonical joint rule for warrant strengths, and a selection the docket may seal."
who: agent
item: "117"
title: "The selection lock: a canonical joint rule for warrant strengths, and a selection the docket may seal"
section: "Deference line — second wave"
maintainer_order: 110
difficulty: "open"
project: normativity.seed
dispatchable: true
item_status: open
deliverable: "the rule and the lock as definitions on `DocketState`, an order-independence theorem for the rule, and the two fixtures (moral: no lock; legal: locked precedent) run through one model."
acceptance: "`python3 tests/run.py` green; the Lean audits clean."
author: "@smithy-verity"
size: M
size_reason: "one item entry of 249 words"
version: 1
---
## Statement
A solution to item 117 ships the rule, the lock, the theorem, and the fixtures.

## Source
PRIORITIES.md, item 117 (The selection lock: a canonical joint rule for warrant strengths, and a selection the docket may seal); its context: `STABILIZATION.md` §4 and `FIXTURES.md` §4 of the round; the queued *Awaiting the author* entry on re-selection and the burn ruling.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
*Re-filed 2026-10-21 by the rebuttal-and-end-to-end round from branch `round/2026-09-16-seed-statics`, where it was item 93; content unchanged; the branch round is landed under `projects/normativity/seed/rounds/2026-09-16-seed-statics/`.*

The seed-statics round (`projects/normativity/seed/rounds/2026-09-16-seed-statics/`)
shows that strength selection among candidate bounds is order-dependent — the same seed
and warrant set end in the disjoint forced intervals `[9/10, 19/20]` and `[3/10, 1/2]`
under the two arrival orders — and that reopening a selection against the whole docket
does not remove it, because both outcomes are maximal joint selections; only reopening
under a fixed canonical rule on joint selections does.  The legal fixture wants the
opposite: *stare decisis* is a selection that must not be reopened, and the docket state
has no object for a sealed selection.  Define the canonical joint rule; define a lock the
docket state can carry; state when a locked selection is a past-self charge (the
2026-08-08 burn ruling, as the dispatch states it) and when it is recomputed state.

*Deliverable shape:* the rule and the lock as definitions on `DocketState`, an
order-independence theorem for the rule, and the two fixtures (moral: no lock; legal:
locked precedent) run through one model.
*Acceptance check:* `python3 tests/run.py` green; the Lean audits clean.

*Context:* `STABILIZATION.md` §4 and `FIXTURES.md` §4 of the round; the queued
*Awaiting the author* entry on re-selection and the burn ruling.
*Consumed by:* any dynamics claim of the form "start from `S`, end in `L`"; the legal
reading of the seed type.
*A solution ships:* the rule, the lock, the theorem, and the fixtures.
