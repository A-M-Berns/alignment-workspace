---
id: item-79
kind: leaf
leaf_kind: task
action: "Execute item 79 per its deliverable shape and acceptance check: Convex representability and compiler completeness for a declared requirement class."
who: agent
item: "79"
title: "Convex representability and compiler completeness for a declared requirement class"
section: "Deference line — second wave"
maintainer_order: 75
difficulty: "open"
project: normativity
dispatchable: true
item_status: open
deliverable: "a Lean definition of the class, a compiler for it, and soundness and completeness theorems with a nonvacuity witness and a requirement outside the class that no row realizes."
acceptance: "the module audits clean and `python3 tests/run.py` is green."
author: "@smithy-verity"
size: M
size_reason: "one item entry of 150 words"
version: 1
---
## Statement
A solution to item 79 ships the class, the compiler, and the two theorems.

## Source
PRIORITIES.md, item 79 (Convex representability and compiler completeness for a declared requirement class); its context: `CONSOLIDATION.md` §9.1 of the mathematical-consolidation round; `NORMATIVE_INDUCTOR_REALIZATION.md` §4 of the realization round for the five properties.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
Compiler soundness, Farkas conflict certification, and conservation on failure are
Lean-proved (`NormativeInductorComposition` §2). What is missing is the object those
theorems are about: a class of anchored requirements — in the consolidation's terms, a
class of `Protocol.Evidence` types — for which a sound finite rational-row realization
over a security fragment exists, and a compiler complete for that class. Keep the five
properties apart: representability of the class, soundness, completeness within the
class, joint feasibility of a serviced bundle, affordable enforceability.

*Deliverable shape:* a Lean definition of the class, a compiler for it, and
soundness and completeness theorems with a nonvacuity witness and a requirement
outside the class that no row realizes.
*Acceptance check:* the module audits clean and `python3 tests/run.py` is green.

*Context:* `CONSOLIDATION.md` §9.1 of the mathematical-consolidation round;
`NORMATIVE_INDUCTOR_REALIZATION.md` §4 of the realization round for the five
properties.
*A solution ships:* the class, the compiler, and the two theorems.
