---
id: item-139
kind: leaf
leaf_kind: task
action: "From a dual-certified market whose account is unbounded below over live prefixes, obtain an efficiently computable staking whose seller exploits, or exhibit such a market that no efficiently computable trader exploits."
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
deliverable: "`lean-proved`; the seller with feature-valued stakes and its value bound, and either the extraction theorem under a stated efficiency hypothesis on the multipliers or the fixture separating an unbounded account from exploitation."
acceptance: "the Lean audit clean; `Condition.seller_netWorth_ge` recovered at constant features; the converse of `DualCertifiedMarket.account_unbounded_of_exploit` proved under the stated hypothesis or refuted by the fixture."
work:
  - {kind: round, ref: projects/normativity/rounds/2026-11-10-exact-conditions-capital}
  - {kind: decision, ref: 2026-11-10--exact-conditions-as-dual-certified-interface}
context: ["lean/Workspace/Normativity/Contrib/ExactConditions.lean", "lean/Workspace/Normativity/Contrib/ExactConditionsFloor.lean", "lean/Workspace/Normativity/Contrib/AssessmentFirm.lean", "projects/normativity/rounds/2026-11-10-exact-conditions-capital/REPORT.md"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, three Lean modules of context"
version: 1
---
## Statement
Item 139, Extraction: from an account unbounded below to an exploiting trader, is delivered in the shape its entry states: `lean-proved`; the seller with feature-valued stakes and its value bound, and either the extraction theorem under a stated efficiency hypothesis on the multipliers or the fixture separating an unbounded account from exploitation.

## Source
ATTENTION.md, item 139 (Extraction: from an account unbounded below to an exploiting trader); its context: `lean/Workspace/Normativity/Contrib/ExactConditions.lean`, `lean/Workspace/Normativity/Contrib/ExactConditionsFloor.lean`, `lean/Workspace/Normativity/Contrib/AssessmentFirm.lean`, `projects/normativity/rounds/2026-11-10-exact-conditions-capital/REPORT.md`.

## Notes
Filed by the exact-conditions round (prompts/2026-11-10-exact-conditions-capital) within its dispatched scope; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
In a dual-certified market, an efficiently computable trader that exploits forces the
account below every bound (`DualCertifiedMarket.account_unbounded_of_exploit`). The converse is
not proved. The market's own multipliers are a staking whose account is bounded above, by
`account_le`, so if the account is also unbounded below `Condition.seller_exploits` would make
the seller staking them exploit — but that seller is defined for rational constants fixed in
advance (`Condition.sellStrategy` trades `EF.const` coefficients), and the multipliers are
functions of the day's prices: in the floor market, the negative part of the firm's aggregate
position on the floored sentence at the posted prices (`FloorSchedule.mu`). Wanted: (a) the
seller with stakes given by expressible features of rank at most the day, and the bound
`seller_netWorth_ge` for it; (b) for the floor market, the multiplier as such a feature — the
firm's position is a finite sum of the features of its day strategy — and what efficiency of
the resulting trader would require, the firm's day strategy growing with the day; (c) the
extraction theorem: an account unbounded below over live prefixes gives an efficiently
computable trader exploiting the market, under whatever hypothesis on the multipliers (b)
shows is needed; or a dual-certified market whose account is unbounded below and which no
efficiently computable trader exploits, in which case boundedness of the account is sufficient
for the criterion and not necessary.

*Deliverable shape:* `lean-proved`; the seller with feature-valued stakes and its value bound, and either the extraction theorem under a stated efficiency hypothesis on the multipliers or the fixture separating an unbounded account from exploitation.
*Acceptance check:* the Lean audit clean; `Condition.seller_netWorth_ge` recovered at constant features; the converse of `DualCertifiedMarket.account_unbounded_of_exploit` proved under the stated hypothesis or refuted by the fixture.
*Context:* `lean/Workspace/Normativity/Contrib/ExactConditions.lean`; `lean/Workspace/Normativity/Contrib/ExactConditionsFloor.lean`; `lean/Workspace/Normativity/Contrib/AssessmentFirm.lean`; `projects/normativity/rounds/2026-11-10-exact-conditions-capital/REPORT.md`.
*Consumed by:* item 137 (with extraction, an account bounded below is necessary as well as sufficient); item 40 (necessity of bounded cumulative liability).
