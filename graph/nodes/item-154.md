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
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`test-supported` — a set of at least twenty cases in which her judgement is bent for a while and she acts on it, each with a published verdict and its citation, coded under `account/BANK_CODING_16.md` and `account/BANK_CODING_17.md` by two coders of different models that have seen no verdict, the answers keyed by case id in files beside `account/bank_coded_16.json`; and a script beside `account/second_coding.py`, wired into `account/run.py`, counting per question the cases on which the two coders agree and the clause's verdicts on the set under each coding against the published verdicts, with predictions committed before the codings; the scorer of `account/case_runs.py` unchanged."
acceptance: "`python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with those counts computed and stated in `account/CASE_RUNS.md`; the predictions' commit earlier than the codings'; no text of a published source in the repository."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-24--legitimacy-statement-working-positions}
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

A judgement bent for a while, which the clause on her earlier rating is ruled to cover,
occurs in four of the 152 bank cases on the first coding of sheet 16 and in ten on the
second, and on neither in a case where a lapse is expected; the clause convicts one of the
four and two of the ten. The prediction written for such cases has gone untested each time.
The sheets were each coded a second time on the bank (`account/CASE_RUNS.md`, last section).
Wanted: a set of cases of bent judgement with published verdicts, coded twice, and the
clause's verdicts on it counted.

*Deliverable shape:* as the entry's deliverable field states.
*Acceptance check:* as the entry's acceptance field states.
*Context:* `CURRENT.md`, `account/CASE_RUNS.md`, `account/case_runs.py`, `account/SECOND_CODING.md`,
`account/second_coding.py`, the two coding sheets, `account/noggle_bank.json` and `account/LEDGER.md`
in the round directory.
*Consumed by:* item 148, and the round that writes the account up.
