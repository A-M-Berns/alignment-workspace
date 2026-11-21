---
id: item-139
kind: leaf
leaf_kind: task
action: "Execute item 139 per its deliverable shape and acceptance check: When the adviser is responsible for her mistake."
who: agent
item: "139"
title: "When the adviser is responsible for her mistake"
section: "Normativity line — legitimacy"
maintainer_order: 151
difficulty: "open"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`test-supported`, or `lean-proved` where a statement is in Lean — a condition on the adviser's courses with the adviser's beliefs an object apart from the truth, computed on the twenty cases of `account/resp_cases.json`, on the forty of `account/intent_cases.json` and on instances I1–I4 of `account/DERIVATION.md`, with the count it decides against the recorded verdict; the avoidable-gain condition of `account/MISTAKES_ACCOUNT.md` §3 is the candidate, computed as that section states it."
acceptance: "`python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with a status for the condition; the number of the twenty cases and of the forty decided wrongly and a stated verdict on I4; any Lean under `lean/Workspace/Deference/Contrib/` builds with `#print axioms` within the three axioms and a witness for each theorem."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-18--legitimacy-working-positions}
  - {kind: decision, ref: 2026-11-21--manipulation-working-positions}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/AGENDA.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/DERIVATION.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/RESP_RESULTS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/resp_cases.json", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/MISTAKES_ACCOUNT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/INTENT_RESULTS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/intent_cases.json"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, one fixture of context"
version: 3
---
## Statement
Item 139, When the adviser is responsible for her mistake, is delivered in the shape its entry states: `test-supported`, or `lean-proved` where a statement is in Lean — a condition on the adviser's courses with the adviser's beliefs an object apart from the truth, computed on the twenty cases of `account/resp_cases.json`, on the forty of `account/intent_cases.json` and on instances I1–I4 of `account/DERIVATION.md`, with the count it decides against the recorded verdict; the avoidable-gain condition of `account/MISTAKES_ACCOUNT.md` §3 is the candidate, computed as that section states it.

## Source
ATTENTION.md, item 139 (When the adviser is responsible for her mistake); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/AGENDA.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/DERIVATION.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/RESP_RESULTS.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/resp_cases.json`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/MISTAKES_ACCOUNT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/INTENT_RESULTS.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/intent_cases.json`.

## Notes
Filed by the fourteenth follow-up to the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution, PROMPT-followup-14.md) under the round prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
The first open problem of `CURRENT.md` §3.

Two tests failed on twenty cases written against them (`account/RESP_RESULTS.md`): the one
that reads the adviser's gain clears an adviser that deceives at a cost to itself and
convicts one that profits by a mistake it did not know of; the one that reads a declared
reference clears a rule that prescribes the manipulation. Six tests of intent on a single
mistake failed on forty more (`account/INTENT_RESULTS.md`).

The account as it stands (`account/MISTAKES_ACCOUNT.md`) keeps Noggle's definition, an
adviser trying to influence her by getting her to make a mistake, leaves "trying to"
unformalised, and gives a checkable property beside it: *avoidable gain*, that another
option open to the adviser was as good otherwise and took less gain through mistakes its
conduct caused, her not knowing, or an unasked shift. Knowingly taking avoidable gain is
acting manipulatively by an argument; the converse fails on five named kinds of case. An
earlier form of the property, read off an outside reviewer's numbers, agrees with that
reviewer's verdict on 37 of forty cases.

Not done: the property as §3 states it has been computed on no case (that needs item 151);
it has not been run on the twenty cases, where a deception at a cost to the adviser takes no
gain and so passes; and what the adviser "believes", its own picture in §5, is not said for
a trained system. Two cases still to be decided, stated as open: an adviser whose honest
errors lean its way by selection (I4), and an adviser that profits from a mistake no course
of its would correct. The maintainer's working positions bear and do not settle it
(`DECISIONS.md`, `2026-11-18--legitimacy-working-positions` and
`2026-11-21--manipulation-working-positions`).

*Deliverable shape:* as the entry's deliverable field states.
*Acceptance check:* as the entry's acceptance field states.
*Context:* `CURRENT.md`, `account/MISTAKES_ACCOUNT.md`, `account/INTENT_RESULTS.md`,
`account/intent_cases.json`, `account/AGENDA.md`, `account/DERIVATION.md`, `account/RESP_RESULTS.md` and
`account/resp_cases.json` in the round directory.
*Consumed by:* item 144 (its classification by responsibility needs the test), and the round that writes
the account up.
