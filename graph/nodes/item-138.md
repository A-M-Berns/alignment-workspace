---
id: item-138
kind: leaf
leaf_kind: task
action: "Derive the bridge's frequency hypothesis on the realized normalized stakes from a frequency statement over efficiently expressible weightings, or exhibit a market where the latter holds and the account is unbounded below."
who: agent
item: "138"
title: "The frequency hypothesis of the conditional bridge, from pseudorandomness"
section: "Normativity line — traderized enforcement"
maintainer_order: 150
difficulty: "open"
heading_notes: ""
project: normativity
dispatchable: true
item_status: open
deliverable: "`lean-proved`; `Bridge.Frequency` for a dual-certified market with one fresh floor per day from a named frequency hypothesis over efficiently expressible weightings, or the counterexample market."
acceptance: "the Lean audit clean; `DualCertifiedMarket.accountBounded_of_frequency` applied with the derived hypothesis to a schedule whose realized values are not all one."
work:
  - {kind: round, ref: projects/normativity/rounds/2026-11-10-exact-conditions-capital}
  - {kind: decision, ref: 2026-11-10--exact-conditions-as-dual-certified-interface}
context: ["lean/Workspace/Normativity/Contrib/ExactConditionsReserve.lean", "lean/Workspace/Normativity/Contrib/ExactConditionsFloor.lean", "lean/Workspace/Normativity/Contrib/WarrantSolvency.lean", "projects/normativity/rounds/2026-11-10-exact-conditions-capital/THEOREM.md"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, three Lean modules of context"
version: 1
---
## Statement
Item 138, The frequency hypothesis of the conditional bridge, from pseudorandomness, is delivered in the shape its entry states: `lean-proved`; `Bridge.Frequency` for a dual-certified market with one fresh floor per day from a named frequency hypothesis over efficiently expressible weightings, or the counterexample market.

## Source
ATTENTION.md, item 138 (The frequency hypothesis of the conditional bridge, from pseudorandomness); its context: `lean/Workspace/Normativity/Contrib/ExactConditionsReserve.lean`, `lean/Workspace/Normativity/Contrib/ExactConditionsFloor.lean`, `lean/Workspace/Normativity/Contrib/WarrantSolvency.lean`, `projects/normativity/rounds/2026-11-10-exact-conditions-capital/THEOREM.md`.

## Notes
Filed by the exact-conditions round (prompts/2026-11-10-exact-conditions-capital) within its dispatched scope; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
One floor `c ≤ price(φ_n)` per day on a fresh sentence settled the next day, with realized
truth values `x_n`. `Bridge.bridge` (registered `exact.conditional-bridge`) bounds the account
below and makes the multipliers summable under two hypotheses: the per-day ceiling, which
`DualCertifiedMarket.account_le` supplies, and `Bridge.Frequency` — if the normalized stakes
`ratio n = μ_n / (U + 1 - Q_{n-1})` are not summable, then eventually their `x`-weighted
partial sums exceed the `c + γ` fraction of their partial sums. The weighting is the market's
own: it is determined by the multipliers the market maker's fixed point produces, and nothing
proved makes it efficiently expressible. The hypothesis is inhabited only where every realized
value is one (`constantFresh_unexploited`), where it holds for any weighting.
`WarrantSolvency.Schema.bounded_iff_frequency` is the same shape with unit stakes: there the
count is unweighted and the bound is an equivalence. Wanted: (a) `Bridge.Frequency` for a
dual-certified market with one fresh floor per day, from the hypothesis that the realized
values have limiting frequency at least `c + γ` along every efficiently expressible weighting
in the sense of the pinned dependency's pseudorandomness properties — which needs the
normalized stakes to be such a weighting, or to be dominated by one; (b) failing that, a
dual-certified market and a truth sequence with frequency above `c + γ` along every such
weighting whose account is unbounded below; (c) the converse reading: whether a failure of
`Bridge.Frequency` yields a staking for `Condition.seller_exploits`.

*Deliverable shape:* `lean-proved`; `Bridge.Frequency` for a dual-certified market with one fresh floor per day from a named frequency hypothesis over efficiently expressible weightings, or the counterexample market.
*Acceptance check:* the Lean audit clean; `DualCertifiedMarket.accountBounded_of_frequency` applied with the derived hypothesis to a schedule whose realized values are not all one.
*Context:* `lean/Workspace/Normativity/Contrib/ExactConditionsReserve.lean`; `lean/Workspace/Normativity/Contrib/ExactConditionsFloor.lean`; `lean/Workspace/Normativity/Contrib/WarrantSolvency.lean`; `projects/normativity/rounds/2026-11-10-exact-conditions-capital/THEOREM.md`.
*Consumed by:* item 61 (solvency of a warrant schema as a frequency statement); item 137.
