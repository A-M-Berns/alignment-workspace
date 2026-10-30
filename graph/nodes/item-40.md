---
id: item-40
kind: leaf
leaf_kind: task
action: "Execute item 40 per its deliverable shape and acceptance check: Is bounded cumulative enforcement liability necessary?."
who: agent
item: "40"
title: "Is bounded cumulative enforcement liability necessary?"
section: "Normativity line — traderized enforcement"
maintainer_order: 18
difficulty: "open"
project: normativity
dispatchable: true
item_status: open
deliverable: "`witness-checked` for a refutation; `derived` or better for necessity."
acceptance: "the trajectory is exhibited in exact rationals with a stated efficiently-computable trader class."
author: "@smithy-verity"
size: M
size_reason: "one item entry of 320 words"
version: 1
---
## Statement
Item 40, Is bounded cumulative enforcement liability necessary, is delivered in the shape its entry states: `witness-checked` for a refutation; `derived` or better for necessity.

## Source
PRIORITIES.md, item 40 (Is bounded cumulative enforcement liability necessary?); its context: `.../2026-08-16-traderized-enforcement/FUNDING_AND_SAFETY.md`, `NORMATIVE_SAFETY.md` §5; `src/outflow.py`.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
**Reframed at the September 2026 checkpoint, not answered.** The affordability
line now builds a substantial theory on top of this hypothesis — persistence,
timeliness, and the endpoint composition all consume it — which raises the item's
value and sharpens what its failure would cost. Until it is settled, every
"unaffordable" verdict in the line means *the known route to safety no longer
applies*, not *no safe policy exists*, and the checkpoint's status ledger says so.
Context: `projects/normativity/legitimacy/checkpoint-2026-09-01/OPEN_PROBLEMS.md` §6.

The preservation theorem's hypothesis is that the enforcement position's
cumulative value over the assessed worlds is bounded below:

    for every n and every ω ∈ Ω_n^live,   Σ_{t≤n} E_t(ω) ≥ −B .

That is sufficient. Its converse is not proved, and one direction of the converse
is known to fail — weak enforcement has zero liability while excluding live worlds
outright, so unbounded liability is not implied by aggressive enforcement.

The item is the necessity direction, or its refutation. If a trajectory can
violate the bound with no efficiently computable trader able to harvest it, that
counterexample is the more valuable outcome, because it would mean the hypothesis
is strictly stronger than the criterion needs and the round's formulation is not
the canonical one.

Note what the item is *not*. It is not about the declared-quantity **certificate**
`Σ_t (ε_t + C_t)·D_t/δ_t`, which is a conservative sufficient upper bound — it
maximizes over the live worlds independently at each date, where the criterion
follows a single world across dates. A certificate that diverges establishes only
that the current proof does not certify safety. The round carries a fixture where
the realized liability at one followed world diverges too, which is the stronger
statement and the one this item's converse would have to engage.

*Deliverable shape:* `witness-checked` for a refutation; `derived` or better for
necessity.
*Acceptance check:* the trajectory is exhibited in exact rationals with a stated
efficiently-computable trader class.
*Context:* `.../2026-08-16-traderized-enforcement/FUNDING_AND_SAFETY.md`,
`NORMATIVE_SAFETY.md` §5; `src/outflow.py`.
