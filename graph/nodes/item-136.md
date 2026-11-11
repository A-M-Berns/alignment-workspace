---
id: item-136
kind: leaf
leaf_kind: task
action: "Construct, for every schedule of nonempty rational polytopes in the cube, a dual-certified market whose condition is the schedule: the constrained fixed point, its rational approximation inside the region, and the multipliers."
who: agent
item: "136"
title: "An exactly compliant market for a schedule of rational polytopes"
section: "Normativity line — traderized enforcement"
maintainer_order: 148
difficulty: "substantial"
heading_notes: ""
project: normativity
dispatchable: true
item_status: open
deliverable: "`lean-proved`; a `DualCertifiedMarket` for every schedule of finitely many floors and ceilings per day, and for every schedule of nonempty rational polytopes given by rows, or the lemma that is missing stated as a Lean proposition with what was tried."
acceptance: "the Lean audit clean; `ExactConditions.FloorSchedule.market`'s condition recovered as an instance of the schedule the construction accepts."
work:
  - {kind: round, ref: projects/normativity/rounds/2026-11-10-exact-conditions-capital}
  - {kind: decision, ref: 2026-11-10--exact-conditions-as-dual-certified-interface}
context: ["lean/Workspace/Normativity/Contrib/ExactConditions.lean", "lean/Workspace/Normativity/Contrib/ExactConditionsFloor.lean", "lean/Workspace/Normativity/Contrib/RowAlternative.lean", "projects/normativity/rounds/2026-11-10-exact-conditions-capital/REPORT.md"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, three Lean modules of context"
version: 1
---
## Statement
Item 136, An exactly compliant market for a schedule of rational polytopes, is delivered in the shape its entry states: `lean-proved`; a `DualCertifiedMarket` for every schedule of finitely many floors and ceilings per day, and for every schedule of nonempty rational polytopes given by rows, or the lemma that is missing stated as a Lean proposition with what was tried.

## Source
ATTENTION.md, item 136 (An exactly compliant market for a schedule of rational polytopes); its context: `lean/Workspace/Normativity/Contrib/ExactConditions.lean`, `lean/Workspace/Normativity/Contrib/ExactConditionsFloor.lean`, `lean/Workspace/Normativity/Contrib/RowAlternative.lean`, `projects/normativity/rounds/2026-11-10-exact-conditions-capital/REPORT.md`.

## Notes
Filed by the exact-conditions round (prompts/2026-11-10-exact-conditions-capital) within its dispatched scope; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
A `DualCertifiedMarket` (`ExactConditions`) is a rational price history over an assessment, a
condition — finitely many demanded bets per day — that the prices satisfy exactly, nonnegative
multipliers, and the day inequality: at every cube valuation the realized trading firm's day
value plus the multiplier-weighted bets is at most the day's tolerance. One exists for every
assessment and every schedule of one floor per day (`ExactConditionsFloor.FloorSchedule.market`,
registered `exact.floor-market`). The day's prices are reparametrized `x = lo + (1 - lo) y`, the
pinned `MarketMaker` prices the firm's strategy with that substitution made in its day-`n` price
features (`liftDay`), and the multiplier on the floor is the size of the firm's negative
aggregate position on the floored sentence; no projection and no duality is used. The day
inequality is proved for an arbitrary lower-bound function (`floor_day_le`), so what one floor
per day restricts is the belief state and the condition's bookkeeping, not the estimate.
Wanted: (a) finitely many floors and ceilings per day — the substitution `lo + (hi - lo) y`,
with the multiplier on a ceiling the positive part of the position; (b) a nonempty rational
polytope `K` per day given by rows: for the day's continuous firm trade `t(p)`, a rational
`p ∈ K` with `t(p)·(y - p) < ε` for every `y ∈ K` — a fixed point of `p ↦ proj_K(p + t(p))` by
the pinned `brouwer_fixed_point`, which is stated for any compact convex set, then a rational
point of `K` near it — and multipliers `μ ≥ 0` with `t(p)·(w - p) + Σ_j μ_j g_j(w) < ε` at
every cube `w`, from the rational alternative `RowAlternative.alternative`; (c) the assembly
into a `DualCertifiedMarket`; (d) `ComputableMarket` for the result, which the floor market
lacks as well: its day step is the pinned search run on a substituted strategy, and no
partial-recursive presentation of the resulting quote table is proved.

*Deliverable shape:* `lean-proved`; a `DualCertifiedMarket` for every schedule of finitely many floors and ceilings per day, and for every schedule of nonempty rational polytopes given by rows, or the lemma that is missing stated as a Lean proposition with what was tried.
*Acceptance check:* the Lean audit clean; `ExactConditions.FloorSchedule.market`'s condition recovered as an instance of the schedule the construction accepts.
*Context:* `lean/Workspace/Normativity/Contrib/ExactConditions.lean`; `lean/Workspace/Normativity/Contrib/ExactConditionsFloor.lean`; `lean/Workspace/Normativity/Contrib/RowAlternative.lean`; `projects/normativity/rounds/2026-11-10-exact-conditions-capital/REPORT.md`.
*Consumed by:* item 137 (a compatibility theorem needs a compliant market to be about); item 139.
