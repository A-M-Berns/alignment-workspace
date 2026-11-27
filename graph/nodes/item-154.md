---
id: item-154
kind: leaf
leaf_kind: task
action: "Execute item 154 per its deliverable shape and acceptance check: A set of cases of bent judgement, coded twice."
who: agent
item: "154"
title: "A set of cases of bent judgement, coded twice"
section: "Normativity line — legitimacy"
maintainer_order: 166
difficulty: "open"
heading_notes: " — *closed: the clause on her earlier rating is not in the statement that governs*"
project: normativity.legitimacy
dispatchable: false
item_status: closed
deliverable: "`test-supported` — a set of at least twenty cases in which her judgement is bent for a while and she acts on it, each with a published verdict and its citation, coded under `account/BANK_CODING_16.md` and `account/BANK_CODING_17.md` by two coders of different models that have seen no verdict, the answers keyed by case id in files beside `account/bank_coded_16.json`; and a script beside `account/second_coding.py`, wired into `account/run.py`, counting per question the cases on which the two coders agree and the clause's verdicts on the set under each coding against the published verdicts, with predictions committed before the codings; the scorer of `account/case_runs.py` unchanged."
acceptance: "`python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with those counts computed and stated in `account/CASE_RUNS.md`; the predictions' commit earlier than the codings'; no text of a published source in the repository."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-24--legitimacy-statement-working-positions}
  - {kind: decision, ref: 2026-11-27--legitimacy-twenty-second-followup-plain-telling}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/CASE_RUNS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/case_runs.py", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/SECOND_CODING.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/second_coding.py", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BANK_CODING_11.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BANK_CODING_16.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/noggle_bank.json", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEDGER.md"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, one fixture of context"
version: 3
---
## Statement
Item 154, A set of cases of bent judgement, coded twice, is delivered in the shape its entry states: `test-supported` — a set of at least twenty cases in which her judgement is bent for a while and she acts on it, each with a published verdict and its citation, coded under `account/BANK_CODING_16.md` and `account/BANK_CODING_17.md` by two coders of different models that have seen no verdict, the answers keyed by case id in files beside `account/bank_coded_16.json`; and a script beside `account/second_coding.py`, wired into `account/run.py`, counting per question the cases on which the two coders agree and the clause's verdicts on the set under each coding against the published verdicts, with predictions committed before the codings; the scorer of `account/case_runs.py` unchanged.

## Source
ATTENTION.md, item 154 (A set of cases of bent judgement, coded twice); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/CASE_RUNS.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/case_runs.py`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/SECOND_CODING.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/second_coding.py`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BANK_CODING_11.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BANK_CODING_16.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/noggle_bank.json`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEDGER.md`.

## Notes
Filed by the sixteenth follow-up to the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution, PROMPT-followup-16.md) under the round prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
Rows 2 and 56 of `account/LEDGER.md`.

Closed without delivery. The item asked for cases of a judgement bent for a while, coded under
sheets 16 and 17, to test the clause on her earlier rating. The statement that governs
(`account/PLAIN_TELLING_STATEMENT.md`) has no such clause: a mood he takes to be moving her is
a mistaken view of what she values, by his lights, and his conduct fails if he could have
told her plainly at another time (the maintainer's rule 8 of 27 November). Sheet 19 asks it
within its second question (`account/BANK_CODING_19.md`), and the adversarial test has one
such case, A16 (`account/PLAIN_TELLING_TESTS.md`).

*Deliverable shape:* as the entry's deliverable field states.
*Acceptance check:* as the entry's acceptance field states.
*Context:* `CURRENT.md`, `account/CASE_RUNS.md`, `account/case_runs.py`, `account/SECOND_CODING.md`,
`account/second_coding.py`, the two coding sheets, `account/noggle_bank.json` and `account/LEDGER.md`
in the round directory.
*Consumed by:* nothing.
