---
id: item-43
kind: leaf
leaf_kind: task
action: "Execute item 43 per its deliverable shape and acceptance check: A compiler that is both exact and safe, or a proof there is none."
who: agent
item: "43"
title: "A compiler that is both exact and safe, or a proof there is none"
section: "Normativity line — traderized enforcement"
maintainer_order: 23
difficulty: "open"
project: normativity
dispatchable: true
item_status: open
deliverable: "`test-supported` for a construction, with the safety and exactness fixtures both green on it; `witness-checked` or `lean-proved` for an impossibility."
acceptance: "the round's existing exactness and safety sweeps, run against the new compiler, both pass."
author: "@smithy-verity"
size: M
size_reason: "one item entry of 231 words"
version: 1
---
## Statement
Item 43 is delivered as its entry specifies; the entry is transcribed below.

## Source
PRIORITIES.md, item 43 (A compiler that is both exact and safe, or a proof there is none); its context: `.../2026-08-16-traderized-enforcement/ENFORCEMENT.md` §5, Theorems 7 through 9; `src/exactness.py`.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
Two compilers, and they are not ordered. The violation-proportional position
never loses in a world its region contains, and cannot force exact membership
against bounded opposing volume. The interior-anchored position forces exact
membership when the region has an interior, and loses in a plausible world at a
price *inside* a world-inclusive region, because it holds positions where there
is no violation at all.

The item is whether the two properties can be had together: a continuous
expressible strategy whose position has a floor outside the region and vanishes
on it. Those pull against each other — a continuous position that vanishes on a
closed region is small just outside it — so a clean impossibility is the expected
outcome and would be worth as much as a construction. Note the two-sided shape:
interior-anchored exactness is proved only for regions with a strict interior, so
the construction question is posed there. Regions with empty interior are **not**
excluded: cube-face settlement pinning is enforced exactly by a constant position,
so a general impossibility claim must not lean on empty interior. Only the earned
geometry is available here.

*Deliverable shape:* `test-supported` for a construction, with the safety and
exactness fixtures both green on it; `witness-checked` or `lean-proved` for an
impossibility.
*Acceptance check:* the round's existing exactness and safety sweeps, run against
the new compiler, both pass.
*Context:* `.../2026-08-16-traderized-enforcement/ENFORCEMENT.md` §5, Theorems 7
through 9; `src/exactness.py`.
