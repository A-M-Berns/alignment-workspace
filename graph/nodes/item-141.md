---
id: item-141
kind: leaf
leaf_kind: task
action: "Express an efficiently computable trader's headroom-normalized short position as a generable weighting of the pinned dependency and bound its gain from selling at the floor under pseudorandomness above the strength, or exhibit the operation that prevents it."
who: agent
item: "141"
title: "One trader's normalized floor-selling as a generable weighting"
section: "Normativity line — traderized enforcement"
maintainer_order: 153
difficulty: "substantial"
heading_notes: ""
project: normativity
dispatchable: true
item_status: open
deliverable: "`lean-proved`; the normalized stake as a `PGenerableWeighting` with the bound on the trader's gain, or the obstruction as a fixture."
acceptance: "the Lean audit clean; `Frequency.gain_bddAbove` or `Bridge.bridge` applied with its frequency hypothesis discharged from the pinned `PseudorandomAbove`."
work:
  - {kind: round, ref: projects/normativity/rounds/2026-11-12-statistical-conditions}
  - {kind: decision, ref: 2026-11-12--statistical-floor-as-threshold-dichotomy}
context: ["lean/Workspace/Normativity/Contrib/StatisticalConditions.lean", "lean/Workspace/Normativity/Contrib/ExactConditionsReserve.lean", "projects/normativity/rounds/2026-11-12-statistical-conditions/THEOREM.md"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, its Lean modules of context"
version: 1
---
## Statement
Item 141, One trader's normalized floor-selling as a generable weighting, is delivered in the shape its entry states: `lean-proved`; the normalized stake as a `PGenerableWeighting` with the bound on the trader's gain, or the obstruction as a fixture.

## Source
ATTENTION.md, item 141 (One trader's normalized floor-selling as a generable weighting); its context: `lean/Workspace/Normativity/Contrib/StatisticalConditions.lean`, `lean/Workspace/Normativity/Contrib/ExactConditionsReserve.lean`, `projects/normativity/rounds/2026-11-12-statistical-conditions/THEOREM.md`.

## Notes
Filed by the statistical-conditions round (prompts/2026-11-12-statistical-conditions) within its dispatched scope; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
`Bridge.bridge` bounds the account of one staker under `Bridge.Frequency` for its own
normalized stake `mu n/(U + 1 − prior n)`, and `Frequency.gain_bddAbove` bounds the gain of
selling at the strength along any weighting of frequency at least it. Neither is connected to
the pinned dependency's `PGenerableWeighting`, `DivergentWeighting` and `PseudorandomAbove`.
Wanted, for an efficiently computable trader whose day-`n` position on `φ n` is a feature of
rank at most `n` and a truth sequence whose values through day `n − 1` are computable in time
polynomial in `n`: (a) the trader's normalized short position as a progression of closed
features satisfying `PGenerableWeighting` — the settled values entering as constants, the
division by the margin through `EF.safeRecip`, which is exact because the margin is at least
one; (b) `Frequency.Along` for it from `PseudorandomAbove` of the centred truth sequence,
the patience clause `DeferralPatient` included; (c) the conclusion, that the trader's
cumulative gain from selling at the floor is bounded. Or the operation that breaks (a).

*Deliverable shape:* `lean-proved`; the normalized stake as a `PGenerableWeighting` with the bound on the trader's gain, or the obstruction as a fixture.
*Acceptance check:* the Lean audit clean; `Frequency.gain_bddAbove` or `Bridge.bridge` applied with its frequency hypothesis discharged from the pinned `PseudorandomAbove`.
*Context:* `lean/Workspace/Normativity/Contrib/StatisticalConditions.lean`; `lean/Workspace/Normativity/Contrib/ExactConditionsReserve.lean`; `projects/normativity/rounds/2026-11-12-statistical-conditions/THEOREM.md`.
*Consumed by:* item 138 (the per-trader half of a bound on the firm's account).
