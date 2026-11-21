---
id: item-148
kind: leaf
leaf_kind: task
action: "Execute item 148 per its deliverable shape and acceptance check: A person's check of a sample of the case encodings."
who: human
item: "148"
title: "A person's check of a sample of the case encodings"
section: "Normativity line — legitimacy"
maintainer_order: 160
difficulty: "open"
heading_notes: ""
project: normativity.legitimacy
dispatchable: false
item_status: open
deliverable: "`test-supported` — a file `account/human_check.json` under the prosecution round holding one person's own verdict, given before seeing the recorded ones, on a stated sample: at least ten of the forty cases of `account/intent_cases.json` (the story against the reviewer's `plainly` and against its numbers), and at least ten of the nineteen value-change cases scored in `account/VC_RESULTS.md` (the case text of `account/LIT_CASES.md` against each reader's verdict); with a module that computes the number on which the person agrees with each recorded verdict, and a results document stating how the sample was drawn."
acceptance: "`python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with those counts computed from `account/human_check.json` and stated in the results document; the sample's ids fixed in the file before any verdict is entered, shown by the order of commits."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/INTENT_RESULTS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/intent_cases.json", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/VC_RESULTS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LIT_CASES.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BLIND_RESULTS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/NOGGLE_RESULTS.md"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, one fixture of context"
version: 1
---
## Statement
Item 148, A person's check of a sample of the case encodings, is delivered in the shape its entry states: `test-supported` — a file `account/human_check.json` under the prosecution round holding one person's own verdict, given before seeing the recorded ones, on a stated sample: at least ten of the forty cases of `account/intent_cases.json` (the story against the reviewer's `plainly` and against its numbers), and at least ten of the nineteen value-change cases scored in `account/VC_RESULTS.md` (the case text of `account/LIT_CASES.md` against each reader's verdict); with a module that computes the number on which the person agrees with each recorded verdict, and a results document stating how the sample was drawn.

## Source
ATTENTION.md, item 148 (A person's check of a sample of the case encodings); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/INTENT_RESULTS.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/intent_cases.json`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/VC_RESULTS.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LIT_CASES.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BLIND_RESULTS.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/NOGGLE_RESULTS.md`.

## Notes
Filed by the fifteenth follow-up to the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution, PROMPT-followup-15.md) under the round prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
The ninth open problem of `CURRENT.md` §3.

Every verdict and encoding behind the counts of `account/INTENT_RESULTS.md`,
`account/BLIND_RESULTS.md`, `account/NOGGLE_RESULTS.md` and `account/VC_RESULTS.md` was
produced by a language model: the outside reviewer wrote the forty cases, their numbers and
their verdicts; Claude readers coded the rest. No person has read a story against its
encoding. Wanted: one person's verdicts on a sample, given before seeing the recorded ones,
and the agreement computed. The cases of Noggle's book cannot be sampled from the
repository, their paraphrases being held outside it; a check of those needs the book.

*Deliverable shape:* as the entry's deliverable field states.
*Acceptance check:* as the entry's acceptance field states.
*Context:* `CURRENT.md`, `account/INTENT_RESULTS.md`, `account/intent_cases.json`, `account/VC_RESULTS.md`,
`account/LIT_CASES.md`, `account/BLIND_RESULTS.md` and `account/NOGGLE_RESULTS.md` in the round directory.
*Consumed by:* items 139 and 144, whose counts rest on these encodings, and the round that writes the account up.
