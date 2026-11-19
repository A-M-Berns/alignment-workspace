---
id: item-147
kind: leaf
leaf_kind: task
action: "Execute item 147 per its deliverable shape and acceptance check: Determining `Legit` of a past stretch from what an overseer can observe."
who: agent
item: "147"
title: "Determining `Legit` of a past stretch from what an overseer can observe"
section: "Normativity line — legitimacy"
maintainer_order: 159
difficulty: "open"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`test-supported` — modules under `account/` of the prosecution round, one per observation model of an overseer, predictions frozen before the code, each saying whether `C` of `ScoringTheorem.Audit` is a function of the record, estimable from it without bias, or neither, with the false-flag and detection rates of D3 that a stated `D` computed from the record attains; and a graded score, continuous in the size of a departure, with its loss on a course that departs with probability ε."
acceptance: "`python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with a status for each observation model; an instance separating *a function of the record* from *estimable without bias* and one separating that from *neither*, in exact rationals; the graded score's loss at ε = 1/10, 1/1000 and 10⁻⁶ at most a stated constant times ε."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/SCORING.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BRIDGE_LEAN.md", "lean/Workspace/Deference/Contrib/ScoringTheorem.lean", "lean/Workspace/Deference/Contrib/AccountJoin.lean", "lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, one fixture of context"
version: 1
---
## Statement
Item 147, Determining `Legit` of a past stretch from what an overseer can observe, is delivered in the shape its entry states: `test-supported` — modules under `account/` of the prosecution round, one per observation model of an overseer, predictions frozen before the code, each saying whether `C` of `ScoringTheorem.Audit` is a function of the record, estimable from it without bias, or neither, with the false-flag and detection rates of D3 that a stated `D` computed from the record attains; and a graded score, continuous in the size of a departure, with its loss on a course that departs with probability ε.

## Source
ATTENTION.md, item 147 (Determining `Legit` of a past stretch from what an overseer can observe); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/SCORING.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BRIDGE_LEAN.md`, `lean/Workspace/Deference/Contrib/ScoringTheorem.lean`, `lean/Workspace/Deference/Contrib/AccountJoin.lean`, `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean`.

## Notes
Filed by the fourteenth follow-up to the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution, PROMPT-followup-14.md) under the round prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
Whether the adviser wronged her on a past stretch is data in the Lean of this line. In
`ScoringTheorem.lean` it is `C`, and what a conduct audit would flag is `D`; the two are
related only by D3 (few false flags, detection at a rate `κ`), a hypothesis, and the
conduct bound reaches `C` only through it (`scoring.conduct-bound`). `Gate.Legit` in
`AccountJoin.lean` is a conjunction of predicates a history carries as fields
(`account/BRIDGE_LEAN.md` §5). Theorem 3 of `DeconfusingCorrigibility.lean` takes
`UnbiasedFromFeedback`, which compares estimates with realized scores that depend on
whether the stretch was legitimate.

Wanted: an observation model for an overseer (what of a stretch is recorded: her inputs,
the adviser's writes, her state, the adviser's policy or samples of it); for each, whether
`C` is a function of the record, estimable from it without bias, or neither, with the case
that separates them; the rates of D3 that an audit `D` computed from the record attains;
and a graded score, continuous in the size of a departure, under which a course that
departs with probability ε loses in proportion to ε.

*Deliverable shape:* as the entry's deliverable field states.
*Acceptance check:* as the entry's acceptance field states.
*Context:* `CURRENT.md`, `account/SCORING.md` and `account/BRIDGE_LEAN.md` in the round directory;
`lean/Workspace/Deference/Contrib/ScoringTheorem.lean`,
`lean/Workspace/Deference/Contrib/AccountJoin.lean` and
`lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean`.
*Consumed by:* item 145 (a design of the audit needs what it can detect), and the corrigibility line's
use of `UnbiasedFromFeedback`.
