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
deliverable: "`test-supported` — a file `account/human_check.json` under the prosecution round holding one person's own answers, given before seeing the recorded ones, on a stated sample: at least twenty cases of the bank of `account/noggle_bank.json`, read in the book, against the questions of `account/BANK_CODING_11.md` and `account/BANK_CODING_16.md`; and at least ten of the forty cases of `account/intent_cases.json` against the first; with a module that computes, per question, the number on which the person agrees with the recorded answer and the number on which the rule's verdict is the same under both, and a results document stating how the sample was drawn."
acceptance: "`python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with those counts computed from `account/human_check.json` and stated in the results document; the sample's ids fixed in the file before any answer is entered, shown by the order of commits."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-24--legitimacy-statement-working-positions}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/CASE_RUNS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/case_runs.py", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/noggle_bank.json", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BANK_CODING_11.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BANK_CODING_16.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/intent_cases.json", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEDGER.md"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, one fixture of context"
version: 2
---
## Statement
Item 148, A person's check of a sample of the case codings, is delivered in the shape its entry states: `test-supported` — a file `account/human_check.json` under the prosecution round holding one person's own answers, given before seeing the recorded ones, on a stated sample: at least twenty cases of the bank of `account/noggle_bank.json`, read in the book, against the questions of `account/BANK_CODING_11.md` and `account/BANK_CODING_16.md`; and at least ten of the forty cases of `account/intent_cases.json` against the first; with a module that computes, per question, the number on which the person agrees with the recorded answer and the number on which the rule's verdict is the same under both, and a results document stating how the sample was drawn.

## Source
ATTENTION.md, item 148 (A person's check of a sample of the case codings); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/CASE_RUNS.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/case_runs.py`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/noggle_bank.json`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BANK_CODING_11.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BANK_CODING_16.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/intent_cases.json`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEDGER.md`.

## Notes
Filed by the fifteenth follow-up to the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution, PROMPT-followup-15.md) under the round prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
Row 51 of `account/LEDGER.md`.

Every answer behind the counts of `account/CASE_RUNS.md` was given by a language model, once.
No person has read a case against its coding. The texts the coders read are paraphrases of
the cases of Noggle's book and are held outside the repository, so a check needs the book.
Wanted: one person's answers on a sample, given before seeing the recorded ones, and the
agreement counted, per question and on the rule's verdict.

*Deliverable shape:* as the entry's deliverable field states.
*Acceptance check:* as the entry's acceptance field states.
*Context:* `CURRENT.md`, `account/CASE_RUNS.md`, `account/case_runs.py`, `account/noggle_bank.json`, the two
coding sheets, `account/intent_cases.json` and `account/LEDGER.md` in the round directory.
*Consumed by:* item 154, whose second coding it calibrates, and the round that writes the account up.
