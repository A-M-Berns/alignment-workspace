---
id: item-144
kind: leaf
leaf_kind: task
action: "Execute item 144 per its deliverable shape and acceptance check: Verdicts on the literature's cases under the present vocabulary."
who: agent
item: "144"
title: "Verdicts on the literature's cases under the present vocabulary"
section: "Normativity line — legitimacy"
maintainer_order: 156
difficulty: "open"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`test-supported` — each case of `account/LIT_CASES.md` in which an adviser acts, classified under the vocabulary of `CURRENT.md` §1 (which of the three wrongs of conduct, attempt or success, legitimate or sound) by two authors independently, with the number on which they agree and the number against a source's verdict."
acceptance: "`python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with a status for the classification; the two counts computed from the two classifications as committed, the first committed before the second author is run."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LIT_CASES.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LIT_RESULTS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/SPEC_RESULTS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/VC_RESULTS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/MISTAKES_ACCOUNT.md"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, one fixture of context"
version: 1
---
## Statement
Item 144, Verdicts on the literature's cases under the present vocabulary, is delivered in the shape its entry states: `test-supported` — each case of `account/LIT_CASES.md` in which an adviser acts, classified under the vocabulary of `CURRENT.md` §1 (which of the three wrongs of conduct, attempt or success, legitimate or sound) by two authors independently, with the number on which they agree and the number against a source's verdict.

## Source
ATTENTION.md, item 144 (Verdicts on the literature's cases under the present vocabulary); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LIT_CASES.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LIT_RESULTS.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/SPEC_RESULTS.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/VC_RESULTS.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/MISTAKES_ACCOUNT.md`.

## Notes
Filed by the fourteenth follow-up to the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution, PROMPT-followup-14.md) under the round prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
The sixth open problem of `CURRENT.md` §3.

`account/VC_RESULTS.md` has two single codings of the bank of `account/LIT_CASES.md`
(Harman, Pettigrew, Kolodny, Carroll et al., Noggle), each by one reader against one
formulation: the account's value-change part agrees with the source on 12 of the 19 cases
whose source judges an act and contradicts none, seven being undecided for facts the
stories do not give. Neither is the classification by two authors independently that this
item asks for, and neither classifies by attempt or success. Where a case is silent on how she
rated beforehand the course that changed her, a verdict follows whichever number is
supplied (`account/SPEC_RESULTS.md`), so the classification records what each author
supplied. The classification by wrong, by attempt and by legitimate against sound can be
made now; a verdict on responsibility waits on item 139.

*Deliverable shape:* as the entry's deliverable field states.
*Acceptance check:* as the entry's acceptance field states.
*Context:* `CURRENT.md`, `account/LIT_CASES.md`, `account/LIT_RESULTS.md` and
`account/SPEC_RESULTS.md` in the round directory.
*Consumed by:* the round that writes the account up.
