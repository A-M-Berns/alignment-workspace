---
id: item-152
kind: leaf
leaf_kind: task
action: "Execute item 152 per its deliverable shape and acceptance check: Comparing whole plans, for an adviser that plans ahead."
who: agent
item: "152"
title: "Comparing whole plans, for an adviser that plans ahead"
section: "Normativity line — legitimacy"
maintainer_order: 164
difficulty: "open"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`test-supported`, or `lean-proved` where a statement is in Lean — a statement of avoidable gain for whole plans compared from the start, in the setting of `account/MISTAKES_ACCOUNT.md` §5, under which a plan that first removes her later honest options and then takes what is left does not pass; with the conclusions of §5 that survive the change and those that do not, each with a proof on paper and an exact search or an instance; and the two-period instance of `account/mistakes_sequential.py` computed from the statement, not put in by hand."
acceptance: "`python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with a status for each conclusion; an exact instance of an adviser that removes her later honest option, on which the decision-by-decision statement of §5 passes every decision and the plan-level statement fails the plan; any Lean under `lean/Workspace/Deference/Contrib/` builds with `#print axioms` within the three axioms and a witness for each theorem."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/MISTAKES_ACCOUNT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/mistakes_sequential.py", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/mistakes_longrun.py", "lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, one fixture of context"
version: 1
---
## Statement
Item 152, Comparing whole plans, for an adviser that plans ahead, is delivered in the shape its entry states: `test-supported`, or `lean-proved` where a statement is in Lean — a statement of avoidable gain for whole plans compared from the start, in the setting of `account/MISTAKES_ACCOUNT.md` §5, under which a plan that first removes her later honest options and then takes what is left does not pass; with the conclusions of §5 that survive the change and those that do not, each with a proof on paper and an exact search or an instance; and the two-period instance of `account/mistakes_sequential.py` computed from the statement, not put in by hand.

## Source
ATTENTION.md, item 152 (Comparing whole plans, for an adviser that plans ahead); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/MISTAKES_ACCOUNT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/mistakes_sequential.py`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/mistakes_longrun.py`, `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean`.

## Notes
Filed by the fifteenth follow-up to the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution, PROMPT-followup-15.md) under the round prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
The thirteenth open problem of `CURRENT.md` §3.

The long-run statement of `account/MISTAKES_ACCOUNT.md` §5 judges avoidable gain at each
decision against the actions then available. An adviser that plans ahead can by earlier
conduct remove her later honest options; at the later decision nothing is then avoidable
and the decision passes. Counting gain that arrives through earlier damage, as §5 does,
does not supply the missing alternative. The outside reviewer raised this of the
two-period example, and in `account/mistakes_sequential.py` which courses pass under each
reading is put in by hand. Wanted: plans compared from the start, which the post's
decision-by-decision setting does not provide.

*Deliverable shape:* as the entry's deliverable field states.
*Acceptance check:* as the entry's acceptance field states.
*Context:* `CURRENT.md`, `account/MISTAKES_ACCOUNT.md`, `account/mistakes_sequential.py` and
`account/mistakes_longrun.py` in the round directory;
`lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean`.
*Consumed by:* item 150 (the Lean statement, if the plan-level form replaces the decision-level one), and the round that writes the account up.
