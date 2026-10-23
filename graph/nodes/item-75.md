---
id: item-75
kind: leaf
leaf_kind: question
action: "Execute PRIORITIES item 75's monotone question: whether enforcing a reason weakly decreases its future depth, so that the persistence criterion survives a closed loop."
who: agent
item: "75"
title: "Close the loop: policy-dependent date costs"
section: "Deference line — second wave"
maintainer_order: 71
difficulty: "entry"
heading_notes: " — *sequenced behind item 74*"
project: normativity
dispatchable: true
item_status: open
deliverable: "a stated theorem with exact-rational fixtures, or a trap instance."
acceptance: "the round's runner is discovered by `python3 tests/run.py` and passes."
context: ["projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/CLOSED_LOOP_EXISTENCE.md"]
author: "@smithy-verity"
size: M
size_reason: "one robustness item"
version: 1
---
## Statement
The persistence criterion survives when enforcing a reason changes its future
depth.

## Source
PRIORITIES.md, item 75 ("Close the loop: policy-dependent date costs");
projects/normativity/legitimacy/checkpoint-2026-09-01/ROADMAP.md, section 4,
which ranks it as robustness work that runs in parallel and "blocks nothing".

## Item
Every existence result in the affordability round is E0-E2 of its own hierarchy: the
date costs `L_t` are exogenous, given to the scheduler by an environment that does not
react. In a live market both inputs to the cost react to the policy. The market
maker's slack and the opposing volume `m_t` respond to how hard the enforcement
position has been pushing, and the exclusion depth `D^r_t` responds to whether the
reason has been enforced — that is the point of enforcing it. So the scheduler's own
spending changes the prices it will face.

Settle E3-E5. The tractable first question is monotone: if enforcing a reason weakly
decreases its future depth, does the persistence criterion survive, and is the greedy
tranche rule still causal-optimal? The adversarial one is whether a policy can be
driven into a friction trap it created — cheap dates spent early, depth restored, and
no affordable dates left.

*Deliverable shape:* a stated theorem with exact-rational fixtures, or a trap
instance.
*Acceptance check:* the round's runner is discovered by `python3 tests/run.py` and
passes.

*Context:*
`projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/CLOSED_LOOP_EXISTENCE.md`
for the hierarchy and what E0-E2 already give, `SHARP_PERSISTENCE.md` for the
exogenous criterion the closed loop has to be compared against, and
`SHARP_TIMELY_SERVICE.md` §6, which names this as the largest gap in its hypotheses.
*A solution ships:* the criterion, and a statement of which of the exogenous theorems
survive the loop unchanged.
