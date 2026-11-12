---
id: item-139
kind: leaf
leaf_kind: task
action: "Prove the buyer near the floor efficiently computable for an efficiently generated sentence sequence, and prove or refute the converse of preservation where the realized frequency near the floor is below the strength."
who: agent
item: "139"
title: "Extraction: from an account unbounded below to an exploiting trader"
section: "Normativity line — traderized enforcement"
maintainer_order: 151
difficulty: "open"
heading_notes: ""
project: normativity
dispatchable: true
item_status: open
deliverable: "`lean-proved`; `EfficientlyComputable` of the buyer near the floor, and either the converse of preservation without the frequency hypothesis or the fixture separating an unbounded account from exploitation."
acceptance: "the Lean audit clean; `DualCertifiedMarket.accountBounded_iff_unexploited` restated without its `EfficientlyComputable` hypothesis for an efficiently generated sentence sequence; the converse of `DualCertifiedMarket.account_unbounded_of_exploit` proved or refuted where `Frequency.Along` fails."
work:
  - {kind: round, ref: projects/normativity/rounds/2026-11-10-exact-conditions-capital}
  - {kind: round, ref: projects/normativity/rounds/2026-11-12-statistical-conditions}
  - {kind: decision, ref: 2026-11-10--exact-conditions-as-dual-certified-interface}
  - {kind: decision, ref: 2026-11-12--statistical-floor-as-threshold-dichotomy}
context: ["lean/Workspace/Normativity/Contrib/ExactConditions.lean", "lean/Workspace/Normativity/Contrib/StatisticalConditions.lean", "lean/Workspace/Normativity/Contrib/ExactConditionsFloor.lean", "lean/Workspace/Normativity/Contrib/AssessmentFirm.lean"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, its Lean modules of context"
version: 2
---
## Statement
Item 139, Extraction: from an account unbounded below to an exploiting trader, is delivered in the shape its entry states: `lean-proved`; `EfficientlyComputable` of the buyer near the floor, and either the converse of preservation without the frequency hypothesis or the fixture separating an unbounded account from exploitation.

## Source
ATTENTION.md, item 139 (Extraction: from an account unbounded below to an exploiting trader); its context: `lean/Workspace/Normativity/Contrib/ExactConditions.lean`, `lean/Workspace/Normativity/Contrib/StatisticalConditions.lean`, `lean/Workspace/Normativity/Contrib/ExactConditionsFloor.lean`, `lean/Workspace/Normativity/Contrib/AssessmentFirm.lean`.

## Notes
Filed by the exact-conditions round (prompts/2026-11-10-exact-conditions-capital) within its dispatched scope and restated by the statistical-conditions round (prompts/2026-11-12-statistical-conditions) to what its results leave; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
In a dual-certified market, an efficiently computable trader that exploits forces the
account below every bound (`DualCertifiedMarket.account_unbounded_of_exploit`). For one floor
per day settled by the next day the converse holds under a frequency hypothesis: if the
realized frequency along the threshold weighting is at least `c + γ`, an account unbounded
below makes `thresholdBuyer` exploit (registered `statistical.bounded-or-buyer-exploits`), and
with that buyer efficiently computable the account is bounded below exactly when no
efficiently computable trader exploits (`DualCertifiedMarket.accountBounded_iff_unexploited`).
The exploiter buys at the floor; it is not the seller of the multipliers. Wanted:
(a) `EfficientlyComputable (thresholdBuyer φ c δ)` for an efficiently generated sentence
sequence `φ`, the buyer's day strategy being one trade whose coefficient is a feature of
constant size; (b) the converse without the frequency hypothesis — where the realized
frequency near the floor is below the strength the candidate exploiter is the seller of the
multipliers, `Condition.seller` with stakes given by expressible features of rank at most the
day, and in the floor market the multiplier is the negative part of the firm's aggregate
position (`FloorSchedule.mu`), a feature of a day strategy that grows with the day — or a
dual-certified market whose account is unbounded below and which no efficiently computable
trader exploits; (c) the same for conditions beyond one floor per day.

*Deliverable shape:* `lean-proved`; `EfficientlyComputable` of the buyer near the floor, and either the converse of preservation without the frequency hypothesis or the fixture separating an unbounded account from exploitation.
*Acceptance check:* the Lean audit clean; `DualCertifiedMarket.accountBounded_iff_unexploited` restated without its `EfficientlyComputable` hypothesis for an efficiently generated sentence sequence; the converse of `DualCertifiedMarket.account_unbounded_of_exploit` proved or refuted where `Frequency.Along` fails.
*Context:* `lean/Workspace/Normativity/Contrib/ExactConditions.lean`; `lean/Workspace/Normativity/Contrib/StatisticalConditions.lean`; `lean/Workspace/Normativity/Contrib/ExactConditionsFloor.lean`; `lean/Workspace/Normativity/Contrib/AssessmentFirm.lean`.
*Consumed by:* item 137 (with extraction, an account bounded below is necessary as well as sufficient); item 40 (necessity of bounded cumulative liability).
