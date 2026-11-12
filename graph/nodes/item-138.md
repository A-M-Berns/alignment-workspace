---
id: item-138
kind: leaf
leaf_kind: task
action: "Decide, for the floor market on a truth sequence with infinitely many false instances, whether the account is bounded below or the buyer near the floor exploits, from a hypothesis that does not mention the market's prices."
who: agent
item: "138"
title: "A statistical floor with infinitely many losses: bounded account or exploited market"
section: "Normativity line — traderized enforcement"
maintainer_order: 150
difficulty: "open"
heading_notes: ""
project: normativity
dispatchable: true
item_status: open
deliverable: "`lean-proved`; a hypothesis on the truth sequence and the assessment under which the floor market's threshold weights are summable, with a witness having infinitely many false instances, or the fixture where they are not."
acceptance: "the Lean audit clean; `DualCertifiedMarket.bounded_or_buyer_exploits` resolved to one disjunct for `FloorSchedule.market` on a truth sequence with infinitely many false instances."
work:
  - {kind: round, ref: projects/normativity/rounds/2026-11-10-exact-conditions-capital}
  - {kind: round, ref: projects/normativity/rounds/2026-11-12-statistical-conditions}
  - {kind: decision, ref: 2026-11-10--exact-conditions-as-dual-certified-interface}
  - {kind: decision, ref: 2026-11-12--statistical-floor-as-threshold-dichotomy}
context: ["lean/Workspace/Normativity/Contrib/StatisticalConditions.lean", "lean/Workspace/Normativity/Contrib/ExactConditionsFloor.lean", "lean/Workspace/Normativity/Contrib/AssessmentFirm.lean", "projects/normativity/rounds/2026-11-12-statistical-conditions/THEOREM.md"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, its Lean modules of context"
version: 2
---
## Statement
Item 138, A statistical floor with infinitely many losses: bounded account or exploited market, is delivered in the shape its entry states: `lean-proved`; a hypothesis on the truth sequence and the assessment under which the floor market's threshold weights are summable, with a witness having infinitely many false instances, or the fixture where they are not.

## Source
ATTENTION.md, item 138 (A statistical floor with infinitely many losses: bounded account or exploited market); its context: `lean/Workspace/Normativity/Contrib/StatisticalConditions.lean`, `lean/Workspace/Normativity/Contrib/ExactConditionsFloor.lean`, `lean/Workspace/Normativity/Contrib/AssessmentFirm.lean`, `projects/normativity/rounds/2026-11-12-statistical-conditions/THEOREM.md`.

## Notes
Filed by the exact-conditions round (prompts/2026-11-10-exact-conditions-capital) within its dispatched scope and restated by the statistical-conditions round (prompts/2026-11-12-statistical-conditions) to what its results leave; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
One floor `c ≤ price(φ_n)` per day on a fresh sentence settled the next day, realized truth
values `x_n`, in a dual-certified market. With at most `R` false instances the account is at
least `−U((1 − c)^-(R+1) − 1)` (`statistical.finite-losses-affordable`), and on sequences a
staker under the per-day ceiling attains that bound. If the prices clear the floor by a margin
from some day on, the account is bounded (`statistical.slack-floor-bounded`). Under realized
frequency at least `c + γ` along the threshold weighting — `thresholdWeight`, one feature of
the day's price — either the account is bounded below or `thresholdBuyer` exploits
(`statistical.bounded-or-buyer-exploits`). `Bridge.Frequency`, the hypothesis of
`exact.conditional-bridge`, holds exactly when the market's normalized stakes are summable
(`bridge_frequency_iff_summable`). On sequences, bounds on each of a family of stakers do not
sum: a mixture of finitely supported tables at weights `θ^R` meets the summed ceiling and its
account is unbounded exactly when `θ ≥ 1 − c` (`statistical.table-mixture-unbounded`). Which
disjunct holds in `FloorSchedule.market` when infinitely many instances are false is not
decided. Wanted: (a) a hypothesis on the truth sequence and the assessment, stated without
reference to the market's prices and mentioning the firm's weights if it must, under which the
threshold weights of `FloorSchedule.market` are summable — hence the account bounded and the
market unexploited — with a witness having infinitely many false instances; or (b) an
assessment, a floor schedule and a truth sequence of limiting frequency above `c + γ` for
which the threshold weights of `FloorSchedule.market` are not summable; (c) in either case,
whether the answer changes with the firm's enumeration `firmRawTrader`, whose weight for the
trader of index `j` sums to `2^-j` over budgets.

*Deliverable shape:* `lean-proved`; a hypothesis on the truth sequence and the assessment under which the floor market's threshold weights are summable, with a witness having infinitely many false instances, or the fixture where they are not.
*Acceptance check:* the Lean audit clean; `DualCertifiedMarket.bounded_or_buyer_exploits` resolved to one disjunct for `FloorSchedule.market` on a truth sequence with infinitely many false instances.
*Context:* `lean/Workspace/Normativity/Contrib/StatisticalConditions.lean`; `lean/Workspace/Normativity/Contrib/ExactConditionsFloor.lean`; `lean/Workspace/Normativity/Contrib/AssessmentFirm.lean`; `projects/normativity/rounds/2026-11-12-statistical-conditions/THEOREM.md`.
*Consumed by:* item 61 (solvency of a warrant schema as a frequency statement); item 137.
