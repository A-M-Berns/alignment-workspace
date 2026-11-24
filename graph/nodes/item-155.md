---
id: item-155
kind: leaf
leaf_kind: task
action: "Execute item 155 per its deliverable shape and acceptance check: The legitimacy statement on cases of value change."
who: agent
item: "155"
title: "The legitimacy statement on cases of value change"
section: "Normativity line — legitimacy"
maintainer_order: 167
difficulty: "open"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`test-supported` — a coding sheet for `account/LEGITIMACY_STATEMENT.md` §1 (what is untold; whether she can pick out and stop what changes her; her rating at her last decision before he began), written with its scorer before any coding; the 90 published cases keyed in `account/vc2_key.json` and the 68 texts and 20 adversarial cases of `account/vc2_cases.json` coded under it by two coders; the counts against the sources' verdicts, the intended verdicts and the outside model's, in `account/CASE_RUNS.md`; and a stated verdict of the statement on the adversarial cases `X6`, `X11` and `X19`."
acceptance: "`python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with those counts computed by `account/case_runs.py` and stated in `account/CASE_RUNS.md`; the scorer's commit earlier than the codings'; no text of a published source in the repository."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-24--legitimacy-statement-working-positions}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEGITIMACY_STATEMENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/CASE_RUNS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/case_runs.py", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/vc2_key.json", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/vc2_cases.json", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEDGER.md"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, one fixture of context"
version: 1
---
## Statement
Item 155, The legitimacy statement on cases of value change, is delivered in the shape its entry states: `test-supported` — a coding sheet for `account/LEGITIMACY_STATEMENT.md` §1 (what is untold; whether she can pick out and stop what changes her; her rating at her last decision before he began), written with its scorer before any coding; the 90 published cases keyed in `account/vc2_key.json` and the 68 texts and 20 adversarial cases of `account/vc2_cases.json` coded under it by two coders; the counts against the sources' verdicts, the intended verdicts and the outside model's, in `account/CASE_RUNS.md`; and a stated verdict of the statement on the adversarial cases `X6`, `X11` and `X19`.

## Source
ATTENTION.md, item 155 (The legitimacy statement on cases of value change); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEGITIMACY_STATEMENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/CASE_RUNS.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/case_runs.py`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/vc2_key.json`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/vc2_cases.json`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEDGER.md`.

## Notes
Filed by the sixteenth follow-up to the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution, PROMPT-followup-16.md) under the round prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
Row 33 of `account/LEDGER.md`.

The statement has no clause for a change in what she values: an influence on her values is
legitimate when nothing that matters is untold, she can pick it out, it does not lead her
against her earlier rating, and she can stop it. It has not been run on a case of value
change. Two earlier forms were, on 23 November (`account/CASE_RUNS.md`): on 90 published
cases they settle about a third, the sources not saying what she knew or whether she could
stop, and on 20 cases an outside model wrote against them they pass three it faults (an
influence switched on over her refusal, an open refusal to broaden her tastes, a change she
asks for that is faulted for its content). The descriptions of the published cases are held
outside the repository and must be supplied to the round. Wanted: the present statement on
the same sets.

*Deliverable shape:* as the entry's deliverable field states.
*Acceptance check:* as the entry's acceptance field states.
*Context:* `CURRENT.md`, `account/LEGITIMACY_STATEMENT.md`, `account/CASE_RUNS.md`, `account/case_runs.py`,
`account/vc2_key.json`, `account/vc2_cases.json` and `account/LEDGER.md` in the round directory.
*Consumed by:* item 141 (her valuing), and the round that writes the account up.
