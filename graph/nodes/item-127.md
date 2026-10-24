---
id: item-127
kind: leaf
leaf_kind: task
action: "Execute item 127 per its deliverable shape and acceptance check: Defeaters as undercutting occurrences: the grounded extension with attacks."
who: agent
item: "127"
title: "Defeaters as undercutting occurrences: the grounded extension with attacks"
section: "Deference line — second wave"
maintainer_order: 120
difficulty: "open"
project: normativity
dispatchable: true
item_status: open
deliverable: "`lean-proved`; the agreement theorem."
acceptance: "the Lean audit clean; `WarrantInductorWitness.survivors_eq` unchanged."
context: ["DECISIONS.md"]
work:
  - {kind: decision, ref: 2026-10-22--survivors-grounded-fixed-point-defeaters-shared}
author: "@smithy-verity"
size: M
size_reason: "one item entry of 146 words"
version: 1
---
## Statement
Item 127, Defeaters as undercutting occurrences: the grounded extension with attacks, is delivered in the shape its entry states: `lean-proved`; the agreement theorem.

## Source
PRIORITIES.md, item 127 (Defeaters as undercutting occurrences: the grounded extension with attacks); its context: `DECISIONS.md` 2026-10-22; `WarrantEntitlement.liveGiven`.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
`Occurrence.defeaters` is read as the ports whose defeat also undercuts the occurrence
(`WarrantEntitlement.undercut`), which makes a warrant's forms share one defeat condition and
makes the survivors the least fixed point of a monotone step. The argumentation-theoretic
reading — a defeater is an *occurrence* that undercuts when it is itself active — makes the
step non-monotone and the right notion the grounded extension of Dung's characteristic
function (defended iff every active attacker is attacked by the set). Wanted: the attack
reading as a second rule on `Grounds`, its grounded extension as a fixed point, the theorem
that the two rules agree when no defeater is an occurrence of the grounds, and a fixture where
an undercutter is itself defeasible.

*Deliverable shape:* `lean-proved`; the agreement theorem.
*Acceptance check:* the Lean audit clean; `WarrantInductorWitness.survivors_eq` unchanged.
*Context:* `DECISIONS.md` 2026-10-22; `WarrantEntitlement.liveGiven`.
*Consumed by:* fixtures with undercutting defeaters that are themselves warrants.
