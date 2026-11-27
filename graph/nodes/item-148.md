---
id: item-148
kind: leaf
leaf_kind: task
action: "Execute item 148 per its deliverable shape and acceptance check: A person's check of a sample of the case codings."
who: human
item: "148"
title: "A person's check of a sample of the case codings"
section: "Normativity line — legitimacy"
maintainer_order: 160
difficulty: "open"
heading_notes: ""
project: normativity.legitimacy
dispatchable: false
item_status: open
deliverable: "`test-supported` — a file `account/human_check.json` under the prosecution round holding one person's own answers, given before seeing the recorded ones, on a stated sample of at least twenty cases of the bank of `account/noggle_bank.json`, read in the book, against the questions of `account/BANK_CODING_19.md`; with a module that computes, per question, the number on which the person agrees with each of the two recorded codings and the number on which the rule's verdict is the same, and a results document stating how the sample was drawn."
acceptance: "`python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with those counts computed from `account/human_check.json` and stated in the results document; the sample's ids fixed in the file before any answer is entered, shown by the order of commits."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-24--legitimacy-statement-working-positions}
  - {kind: decision, ref: 2026-11-27--legitimacy-twenty-second-followup-plain-telling}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/PLAIN_TELLING_TESTS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/plain_telling_tests.py", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/noggle_bank.json", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BANK_CODING_19.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/bank_coded_19_1.json", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/bank_coded_19_2.json", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEDGER.md"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, one fixture of context"
version: 3
---
## Statement
Item 148, A person's check of a sample of the case codings, is delivered in the shape its entry states: `test-supported` — a file `account/human_check.json` under the prosecution round holding one person's own answers, given before seeing the recorded ones, on a stated sample of at least twenty cases of the bank of `account/noggle_bank.json`, read in the book, against the questions of `account/BANK_CODING_19.md`; with a module that computes, per question, the number on which the person agrees with each of the two recorded codings and the number on which the rule's verdict is the same, and a results document stating how the sample was drawn.

## Source
ATTENTION.md, item 148 (A person's check of a sample of the case codings); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/PLAIN_TELLING_TESTS.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/plain_telling_tests.py`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/noggle_bank.json`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BANK_CODING_19.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/bank_coded_19_1.json`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/bank_coded_19_2.json`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEDGER.md`.

## Notes
Filed by the fifteenth follow-up to the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution, PROMPT-followup-15.md) under the round prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
Rows 51 and 101 of `account/LEDGER.md`.

Every answer behind the counts of `account/PLAIN_TELLING_TESTS.md` and `account/CASE_RUNS.md` was
given by a language model. No person has read a case against its coding. The texts the
coders read are paraphrases of the cases of Noggle's book and are held outside the
repository, so a check needs the book. Wanted: one person's answers on a sample, given
before seeing the recorded ones, and the agreement counted, per question and on the rule's
verdict.

First in the maintainer's ordering of 27 November. A sheet of twenty cases is prepared
outside the repository and awaits him (`DECISIONS.md`,
`open--maintainer-check-of-twenty-codings`).

*Deliverable shape:* as the entry's deliverable field states.
*Acceptance check:* as the entry's acceptance field states.
*Context:* `CURRENT.md`, `account/PLAIN_TELLING_TESTS.md`, `account/plain_telling_tests.py`, `account/noggle_bank.json`,
`account/BANK_CODING_19.md`, the two codings of run 19 and `account/LEDGER.md` in the round directory.
*Consumed by:* the round that writes the account up.
