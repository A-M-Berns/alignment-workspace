---
id: item-139
kind: leaf
leaf_kind: task
action: "Execute item 139 per its deliverable shape and acceptance check: What the adviser believes and expects, for a trained system."
who: agent
item: "139"
title: "What the adviser believes and expects, for a trained system"
section: "Normativity line — legitimacy"
maintainer_order: 151
difficulty: "open"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`test-supported`, or `lean-proved` where a statement is in Lean — a stated procedure that yields, for a system and an episode, the weights and expected courses that `LegitimacyModel.Model` takes as his picture (`μ`, `st`, `act`, `course`), with one instance in which a system whose reported picture differs from the one it acts on is told apart from a sincere one, and one instance in which it cannot be."
acceptance: "`python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with both instances computed in exact rationals and a status for each; any Lean under `lean/Workspace/Deference/Contrib/` builds with `#print axioms` within the three axioms and a witness for each theorem."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-24--legitimacy-statement-working-positions}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEGITIMACY_STATEMENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEDGER.md", "lean/Workspace/Deference/Contrib/LegitimacyModel.lean"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, one fixture of context"
version: 4
---
## Statement
Item 139, What the adviser believes and expects, for a trained system, is delivered in the shape its entry states: `test-supported`, or `lean-proved` where a statement is in Lean — a stated procedure that yields, for a system and an episode, the weights and expected courses that `LegitimacyModel.Model` takes as his picture (`μ`, `st`, `act`, `course`), with one instance in which a system whose reported picture differs from the one it acts on is told apart from a sincere one, and one instance in which it cannot be.

## Source
ATTENTION.md, item 139 (What the adviser believes and expects, for a trained system); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEGITIMACY_STATEMENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEDGER.md`, `lean/Workspace/Deference/Contrib/LegitimacyModel.lean`.

## Notes
Filed by the fourteenth follow-up to the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution, PROMPT-followup-14.md) under the round prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
Rows 1 and 2 of `account/LEDGER.md`.

The statement of `account/LEGITIMACY_STATEMENT.md` judges an adviser's conduct by his own
lights: what is untold is what he believes and has not said, an effect is one he expects, and
a sincere adviser who is wrong satisfies it. In `LegitimacyModel.lean` his lights are the
weights `μ` on a finite set of cases and, for each set of his moves, the course he expects.
Nothing says what those are for a trained system, and the whole verdict rests on them: two
systems that act alike and differ in what they expect of her get different verdicts.
Wanted: a procedure that produces the picture, and the two instances that show what it can
and cannot tell apart.

*Deliverable shape:* as the entry's deliverable field states.
*Acceptance check:* as the entry's acceptance field states.
*Context:* `CURRENT.md`, `account/LEGITIMACY_STATEMENT.md` and `account/LEDGER.md` in the round directory;
`lean/Workspace/Deference/Contrib/LegitimacyModel.lean`.
*Consumed by:* item 147 (what a gate can observe), and the round that writes the account up.
