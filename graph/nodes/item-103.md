---
id: item-103
kind: leaf
leaf_kind: task
action: "Execute item 103 per its deliverable shape and acceptance check: A decision theory for logical inductors without the split between a belief market and a choice learner."
who: agent
item: "103"
title: "A decision theory for logical inductors without the split between a belief market and a choice learner"
section: "Deference line — second wave"
maintainer_order: 96
difficulty: "open"
project: deference
dispatchable: true
item_status: open
deliverable: "a single learner over the inductor that satisfies the extension's decision interface (evaluations of the stated form; a maximizer off exploration; exploration in the permitted set; overestimation `B(K) = o(K)`) with explicit accounting of `B(K)`; Lean where the pinned formalization admits it, paper-level elsewhere with named hypotheses."
acceptance: "`python3 tests/run.py` green; Lean audits clean; the extension's rate theorem instantiated on the learner (`realized_rate`) with its `B(K)` discharged rather than assumed."
work:
  - {kind: decision, ref: 2026-09-27--decision-theory-logical-inductors-without-belief}
author: "@smithy-verity"
size: M
size_reason: "one item entry of 253 words"
version: 1
---
## Statement
A solution to item 103 ships the learner with its accounting, or the obstruction.

## Source
PRIORITIES.md, item 103 (A decision theory for logical inductors without the split between a belief market and a choice learner); its context: the phase-2 round's `SPEC.md` §6 and `REPORT.md`; `KernelExtension.lean`; `Continuation-BRIA.md` §9 (the LI coupling); items 86, 90, 102.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
The kernel's extension (`projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md`
§6) realizes the decision interface twice — Continuation BRIA beside the inductor, and a
maximizer over the inductor with exploration restricted to the permitted set — and both
keep the split the pinned Logical Induction paper leaves open: the market prices sentences,
a separate learner chooses, and the coupling is a named hypothesis (unbiasedness from
feedback; the auction's budget accounting).  The known pathologies of argmax over the
inductor's own-action conditionals live in that split.  Wanted: a principled decision
theory for logical inductors with no separate choice learner.  The candidate direction:
claims of the form "if chosen, this option scores `x`" as securities of the inductor,
settled only when the option is chosen, with a choice rule that forces tests of options
promised to be better — the bounded-inductive-rationality criterion stated inside the
market rather than beside it.

*Deliverable shape:* a single learner over the inductor that satisfies the extension's
decision interface (evaluations of the stated form; a maximizer off exploration;
exploration in the permitted set; overestimation `B(K) = o(K)`) with explicit accounting of
`B(K)`; Lean where the pinned formalization admits it, paper-level elsewhere with named
hypotheses.
*Acceptance check:* `python3 tests/run.py` green; Lean audits clean; the extension's rate
theorem instantiated on the learner (`realized_rate`) with its `B(K)` discharged rather
than assumed.
*Context:* the phase-2 round's `SPEC.md` §6 and `REPORT.md`; `KernelExtension.lean`;
`Continuation-BRIA.md` §9 (the LI coupling); items 86, 90, 102.
*Consumed by:* the extension's exploration realization; item 102's re-scoped question.
*A solution ships:* the learner with its accounting, or the obstruction.
