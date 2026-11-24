---
id: item-154
kind: leaf
leaf_kind: task
action: "Execute item 154 per its deliverable shape and acceptance check: A second coding of the bank, and a set of cases of bent judgement."
who: agent
item: "154"
title: "A second coding of the bank, and a set of cases of bent judgement"
section: "Normativity line — legitimacy"
maintainer_order: 166
difficulty: "open"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`test-supported` — `account/BANK_CODING_11.md` and `account/BANK_CODING_16.md` each coded again by a coder that has seen neither the first coding nor a verdict, the answers keyed by case id in files beside the first; a set of at least twenty cases in which her judgement is bent for a while and she acts on it, each with a published verdict and its citation, coded twice under sheet 16; and `account/case_runs.py` extended to count, per question, the cases on which the two coders agree, the rule's verdicts under each coding, and the clause's verdicts on the new set, with predictions written before the codings."
acceptance: "`python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with those counts computed and stated in `account/CASE_RUNS.md`; the scorer's commit earlier than the codings'; no text of a published source in the repository."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-24--legitimacy-statement-working-positions}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/CASE_RUNS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/case_runs.py", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BANK_CODING_11.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BANK_CODING_16.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/noggle_bank.json", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEDGER.md"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, one fixture of context"
version: 1
---
## Statement
Item 154, A second coding of the bank, and a set of cases of bent judgement, is delivered in the shape its entry states: `test-supported` — `account/BANK_CODING_11.md` and `account/BANK_CODING_16.md` each coded again by a coder that has seen neither the first coding nor a verdict, the answers keyed by case id in files beside the first; a set of at least twenty cases in which her judgement is bent for a while and she acts on it, each with a published verdict and its citation, coded twice under sheet 16; and `account/case_runs.py` extended to count, per question, the cases on which the two coders agree, the rule's verdicts under each coding, and the clause's verdicts on the new set, with predictions written before the codings.

## Source
ATTENTION.md, item 154 (A second coding of the bank, and a set of cases of bent judgement); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/CASE_RUNS.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/case_runs.py`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BANK_CODING_11.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BANK_CODING_16.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/noggle_bank.json`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEDGER.md`.

## Notes
Filed by the sixteenth follow-up to the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution, PROMPT-followup-16.md) under the round prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
Rows 3, 6, 7, 8, 10 and 35 of `account/LEDGER.md`.

The disclosure rule and the clause on her earlier rating each rest on one coding of the bank
of cases from Noggle's book by one language model: 214 of 219 settled cases for the first,
33 of 33 for the second, with one control convicted. The rule was formed with the bank in
view. Three questions worded alike on two sheets were answered alike by two coders on 142,
142 and 148 of 152 cases, which is the only measure of agreement there is. A judgement bent
for a while, which the clause is ruled to cover, occurs in four of the 152 cases as coded
and in none of those where a lapse is expected. The paraphrases the coders read are outside
the repository and must be supplied to the round. Wanted: each sheet coded a second time,
and a set of cases of bent judgement.

*Deliverable shape:* as the entry's deliverable field states.
*Acceptance check:* as the entry's acceptance field states.
*Context:* `CURRENT.md`, `account/CASE_RUNS.md`, `account/case_runs.py`, the two coding sheets,
`account/noggle_bank.json` and `account/LEDGER.md` in the round directory.
*Consumed by:* item 148, and the round that writes the account up.
