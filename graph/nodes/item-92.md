---
id: item-92
kind: leaf
leaf_kind: task
action: "Execute item 92 per its deliverable shape and acceptance check: The reason-side supply obligation: the realization's protection rule and the general-cost optimum."
who: agent
item: "92"
title: "The reason-side supply obligation: the realization's protection rule and the general-cost optimum"
section: "Deference line — second wave"
maintainer_order: 88
difficulty: "open"
heading_notes: " — *narrowed 2026-09-16: the service half is a theorem (`ReasonSupply.lean`: suffix-cut obstruction, hybrid bound, composition `li_noncapture`) and is canonical; what remains is the realization's choice of protected set (`hybrid_bound`'s rule, recorded not adopted) and the general-cost weighted optimum beyond the cut bound; the discovery residual is item 93*"
project: deference
dispatchable: true
item_status: open
deliverable: "a clause with its discharge condition (who supplies, by when, at what budget), an exact fixture in which the supply obligation is met and the content residual against the fully-informed comparator is zero on every audited world, and the timeliness-affordability bound for the supplier."
acceptance: "`python3 tests/run.py` green; Lean audits clean."
context: ["wiki/Openness-Coverage-and-Non-Capture.md"]
author: "@smithy-verity"
size: L
size_reason: "one item entry of 431 words"
version: 1
---
## Statement
A solution to item 92 ships the clause and its fixture, or the negative — that no affordable supply obligation exists under the deadline for the declared interface — with its witness.

## Source
PRIORITIES.md, item 92 (The reason-side supply obligation: the realization's protection rule and the general-cost optimum); its context: `REASON_INTERFACE.md` §3 and `AFFORDABILITY_INTERFACE.md` §§1–3 of the round; `wiki/Openness-Coverage-and-Non-Capture.md` (route availability is not exercise); item 87 clause 5 (protected reason-supply liveness) for the protected half of the same obligation.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
The non-capture compilation round (`projects/deference/rounds/2026-09-16-noncapture-compilation/`)
compiles the trace-steering inequality into the landed corrigibility constraint and
refutes the thesis that completeness, authentication, canonicalization, coverage and
liveness of a declared reason interface remove the residual: a true unprotected declared
counterreason nobody raises passes every clause and is worth its weight (fixture 2).
The residual against the fully-informed comparator is removed by exactly one of two
decisions that are not interface properties — total protected scope (every declared
reason type protected, so an omission voids; `content_residual_zero_of_total_scope`) or
a supply obligation on the registrar, the engine or third parties to raise every true
declared reason before the commitment deadline.  Under the deadline the second is the
affordability theory's timeliness case: budgets add and declared reasons compete.
Decide which the realization adopts, state the supply obligation as a clause of the
evaluation-ecosystem bill alongside item 87's clause 5, and give the bounded-delay
criterion for it; then the strengthened two-interface statement of the round's
`REASON_INTERFACE.md` §5 is a candidate for canonicalization.

*Update 2026-09-16 (second pass of the round).*  The supply obligation now has a theorem:
with the docket's release times and costs and the supplier's capacity, every true declared
reason is served before commitment iff every suffix cut is underwritten
(`unit_servable_iff_cut`), the least missed adverse mass is the layered cut excess, and the
certified bound composes with the landed inequality (`li_noncapture`).  What is left for
this item: (a) the realization's choice of protected set — the round records the rule
"protect a servable set of largest adverse mass" (`hybrid_bound`) and does not adopt it;
(b) the exogenous-cost hypothesis (the advisor must not be able to raise a counterreason's
service cost); (c) the discovery residual, the adverse mass of true declared reasons no
independent process raises before commitment, which is an inquiry question and not a
service one.

*Deliverable shape:* a clause with its discharge condition (who supplies, by when, at
what budget), an exact fixture in which the supply obligation is met and the content
residual against the fully-informed comparator is zero on every audited world, and the
timeliness-affordability bound for the supplier.
*Acceptance check:* `python3 tests/run.py` green; Lean audits clean.

*Context:* `REASON_INTERFACE.md` §3 and `AFFORDABILITY_INTERFACE.md` §§1–3 of the round;
`wiki/Openness-Coverage-and-Non-Capture.md` (route availability is not exercise); item 87
clause 5 (protected reason-supply liveness) for the protected half of the same
obligation.
*Consumed by:* any canonicalization of the reason-side corrigibility inequality; the
measurability claims of the round's `AFFORDABILITY_INTERFACE.md` §4.
*A solution ships:* the clause and its fixture, or the negative — that no affordable
supply obligation exists under the deadline for the declared interface — with its
witness.
