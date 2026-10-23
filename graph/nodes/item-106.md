---
id: item-106
kind: and
children: [li-bria-milestones-met, item-105, integration-theorem-t10, li-bria-obstruction-advance, item-106.complete]
item: "106"
title: "A candidate LI/BRIA synthesis against the acceptance statement"
section: "Deference line — second wave"
maintainer_order: 99
difficulty: "open"
project: decision-theory
dispatchable: true
item_status: open
deliverable: "the construction with its existence proof; the checklist, item by item, with what is proved, what is fixture-supported, and what is not shown; the suite's rows scored with exact fixtures."
acceptance: "`python3 tests/run.py` green; Lean audits clean if any."
context: ["wiki/Continuation-BRIA.md"]
author: "@smithy-verity"
size: M
size_reason: "three round documents and two PRIORITIES items"
version: 1
---
## Statement
A computable agent combining logical induction and bounded inductive
rationality meets the acceptance statement: milestones M1 to M4 and the
integration obligation I1 to I3 jointly, with the strong belief–decision
compatibility form, the integration theorem T10, and one advance on a
recognized obstruction of logical-induction decision theory.

## Source
PRIORITIES.md, item 106 (a candidate LI/BRIA synthesis against the acceptance
statement) and
projects/decision-theory/rounds/2026-09-29-li-bria-synthesis-spec/PROBLEM_STATEMENT.md,
section 0;
projects/decision-theory/rounds/2026-09-29-li-bria-synthesis-spec/REPORT.md,
section 7: "Whether the milestones, I1, I3 and A1 are *jointly* achievable by
any computable agent is not known".

## Notes
The endpoint PRIORITIES.md item 106 sets for the LI/BRIA line, shared with the updateful trust
line if it files the decision layer. Four conjuncts named by the acceptance
statement itself, each a step with the round's work order behind it; the line
has registered no theorem yet.

## Item
Construct a computable agent and check it against `projects/decision-theory/rounds/2026-09-29-li-bria-synthesis-spec/PROBLEM_STATEMENT.md` §0 and
its checklist §9: the supporting milestones M1–M4 with the four recovery domains of M3
declared and the commitment source of M5 named; the integration obligation of §3 — the
five exhibits, I1 proved on a stated environment class with explicit computational
accounting (the four steps of T10), I3 proved on the belief-disagreement environment
a failure mode specified to §7's qualification standard (A1 is the proposed, provisional
instance), I2 at least as W1 (item 105); the recovery and integration rows of `TEST_SUITE.md`
passed under their assumptions and the construction-level rows reported, each with its
access model, scored unit and any supplied channel, contract, oracle or menu
restriction stated against the primary source; and the advance — by a diagnostic
meeting the qualification standard of §7 (A1 is a proposed, provisional instance), one
theorem being allowed to discharge both I3 and the advance.  Updatelessness (A2) is an extension,
and a candidate claiming it declares its recovery domain and states that the domain
question of M3 is open.  The continuation-BRIA specialization is one admissible shape.
A candidate meeting the milestones and I1 alone is an integration theorem, reported as
such and not as the endpoint.

*Deliverable shape:* the construction with its existence proof; the checklist, item by
item, with what is proved, what is fixture-supported, and what is not shown; the suite's
rows scored with exact fixtures.
*Acceptance check:* `python3 tests/run.py` green; Lean audits clean if any.
*Context:* the round's three documents; `wiki/Continuation-BRIA.md` for the
specialization; items 86, 91, 102, 105.
*Consumed by:* the decision-theory line's first registered claims; the deference line's
learning layer if the construction realizes the coupling of item 102.
*A solution ships:* the construction against the acceptance statement, or a proof that
some obligation is unsatisfiable by any computable agent, which reopens the
specification.
