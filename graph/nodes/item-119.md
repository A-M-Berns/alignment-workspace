---
id: item-119
kind: leaf
leaf_kind: task
action: "Execute item 119 per its deliverable shape and acceptance check: Hidden discord: a region-level convergence measure."
who: agent
item: "119"
title: "Hidden discord: a region-level convergence measure"
section: "Deference line — second wave"
maintainer_order: 112
difficulty: "open"
project: normativity.seed
dispatchable: true
item_status: open
deliverable: "the definition on `IntervalData` or on regions, the analogue of `discord_persists`, and the two hidden-discord fixtures scored positive by it."
acceptance: "`python3 tests/run.py` green; the Lean audits clean."
author: "@smithy-verity"
size: M
size_reason: "one item entry of 211 words"
version: 1
---
## Statement
A solution to item 119 ships the component, its monotonicity theorem, and the fixtures.

## Source
PRIORITIES.md, item 119 (Hidden discord: a region-level convergence measure); its context: `MANY.md` §2 and `GAMEABILITY.md` (what is not blocked) of the round.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
*Re-filed 2026-10-21 by the rebuttal-and-end-to-end round from branch `round/2026-09-17-convergence-measure`, where it was item 95; content unchanged; the branch round is landed under `projects/normativity/seed/rounds/2026-09-17-convergence-measure/`.*

The convergence-measure round (`projects/normativity/seed/rounds/2026-09-17-convergence-measure/`)
shows that the coordinate-wise profile `(Hull, Ovl, Disc)` on a declared fragment can
report `Disc = 0` while the merged bundle is infeasible — two humble reasoners holding
`y ≥ (9/10)x, x ≥ (9/10)y` and `x ≥ 4/5, y ≤ 3/10`, and three reasoners pairwise
compatible and jointly not (`hidden_discord`).  Helly in dimension one makes coordinate
discord pairwise (`discord_iff_pair`); nothing makes merged feasibility so.  No
declaration of fragment or weights blocks this.  Define a region-level component of the
profile — a merged-feasibility mass, or a relational discord over declared *pairs* of
sentences, or the affine dimension of the merged region — that sees relational
incompatibility, prove its monotonicity under nesting, and give its certificate.

*Deliverable shape:* the definition on `IntervalData` or on regions, the analogue of
`discord_persists`, and the two hidden-discord fixtures scored positive by it.
*Acceptance check:* `python3 tests/run.py` green; the Lean audits clean.

*Context:* `MANY.md` §2 and `GAMEABILITY.md` (what is not blocked) of the round.
*Consumed by:* any use of `Disc = 0` as "the reasoners could jointly hold their bundles".
*A solution ships:* the component, its monotonicity theorem, and the fixtures.
