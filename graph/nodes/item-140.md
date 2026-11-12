---
id: item-140
kind: leaf
leaf_kind: task
action: "Build an assessment over a probability space of observations on which the floor market's multipliers and realized values satisfy the hypotheses of the capital bound, and conclude an account bounded below along almost every path."
who: agent
item: "140"
title: "A floor market driven by random observations: the capital bound path by path"
section: "Normativity line — traderized enforcement"
maintainer_order: 152
difficulty: "open"
heading_notes: ""
project: normativity
dispatchable: true
item_status: open
deliverable: "`lean-proved`; the assessment over an observation space, `Betting.Fair` for the floor market's multipliers on it, and an account bounded below along almost every path; or the fixture where an unsettled instance breaks it."
acceptance: "the Lean audit clean; `Betting.Fair.ae_bounded_below` applied to `FloorSchedule.market` over the constructed assessment, with a witness whose outcomes are not almost surely one."
work:
  - {kind: round, ref: projects/normativity/rounds/2026-11-12-statistical-conditions}
  - {kind: decision, ref: 2026-11-12--statistical-floor-as-threshold-dichotomy}
context: ["lean/Workspace/Normativity/Contrib/StatisticalConditionsVille.lean", "lean/Workspace/Normativity/Contrib/StatisticalConditions.lean", "lean/Workspace/Normativity/Contrib/ExactConditionsFloor.lean", "lean/Workspace/Normativity/Contrib/AssessmentProcess.lean", "projects/normativity/rounds/2026-11-12-statistical-conditions/THEOREM.md"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, its Lean modules of context"
version: 1
---
## Statement
Item 140, A floor market driven by random observations: the capital bound path by path, is delivered in the shape its entry states: `lean-proved`; the assessment over an observation space, `Betting.Fair` for the floor market's multipliers on it, and an account bounded below along almost every path; or the fixture where an unsettled instance breaks it.

## Source
ATTENTION.md, item 140 (A floor market driven by random observations: the capital bound path by path); its context: `lean/Workspace/Normativity/Contrib/StatisticalConditionsVille.lean`, `lean/Workspace/Normativity/Contrib/StatisticalConditions.lean`, `lean/Workspace/Normativity/Contrib/ExactConditionsFloor.lean`, `lean/Workspace/Normativity/Contrib/AssessmentProcess.lean`, `projects/normativity/rounds/2026-11-12-statistical-conditions/THEOREM.md`.

## Notes
Filed by the statistical-conditions round (prompts/2026-11-12-statistical-conditions) within its dispatched scope; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
`Betting.Fair.account_bound` (registered `statistical.capital-bound-probability`): outcomes
`x n ∈ [0, 1]` with conditional expectation at least `c` given the past, predictable stakes
`mu n ≥ 0` and the per-day ceiling give a settled account that reaches `−K` with probability
at most `U/(U + K)` and is almost surely bounded below. No market is involved. Wanted: a
probability space of observation sequences and an assessment whose worlds live at `N` are
those agreeing with the observations through `N`, such that (a) the multiplier of
`FloorSchedule.market` on day `n` is measurable in the observations before day `n`; (b) the
settlement hypotheses of `DualCertifiedMarket.account_ge_of_losses` hold along each path;
(c) the realized values have conditional expectation at least `c` given the earlier
observations. Then `Betting.Fair` holds for the market's multipliers and realized values, and
along almost every path the account is bounded below over live prefixes, the open instance
costing a factor `(1 − c)⁻¹` over the settled account. To be decided on the way: an instance
that is true and never settled stays open with both values in every later live world, and the
supermartingale step does not occur for it — the settlement schedule under which the bound
survives, or the fixture where it fails.

*Deliverable shape:* `lean-proved`; the assessment over an observation space, `Betting.Fair` for the floor market's multipliers on it, and an account bounded below along almost every path; or the fixture where an unsettled instance breaks it.
*Acceptance check:* the Lean audit clean; `Betting.Fair.ae_bounded_below` applied to `FloorSchedule.market` over the constructed assessment, with a witness whose outcomes are not almost surely one.
*Context:* `lean/Workspace/Normativity/Contrib/StatisticalConditionsVille.lean`; `lean/Workspace/Normativity/Contrib/StatisticalConditions.lean`; `lean/Workspace/Normativity/Contrib/ExactConditionsFloor.lean`; `lean/Workspace/Normativity/Contrib/AssessmentProcess.lean`; `projects/normativity/rounds/2026-11-12-statistical-conditions/THEOREM.md`.
*Consumed by:* item 138 (a probabilistic sufficient condition for its first disjunct); item 61 (solvency of a warrant schema as a frequency statement).
