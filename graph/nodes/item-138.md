---
id: item-138
kind: leaf
leaf_kind: task
action: "Execute item 138 per its deliverable shape and acceptance check: The cases and the prior work: the present vocabulary on the bank of published cases, and what is new."
who: agent
item: "138"
title: "The cases and the prior work: the present vocabulary on the bank of published cases, and what is new"
section: "Normativity line — legitimacy"
maintainer_order: 150
difficulty: "open"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`test-supported` — (a) each case of `account/LIT_CASES.md` in which an adviser acts, classified under the vocabulary of `CURRENT.md` §1 (which of the three wrongs of conduct, attempt or success, legitimate or sound) by two authors independently, with the number on which they agree and the number against a source's verdict; (b) a document setting the scoring theorem and the two measures beside reward tampering, path-specific objectives, eliciting latent knowledge and induced preference shifts, saying of each whether the result is an instance of the published one or giving an instance that separates them."
acceptance: "`python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with a status for each lettered part; for (a) the two counts computed from the two classifications as committed, the first committed before the second author is run; for (b) each separating instance in exact rationals."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-10--legitimacy-prosecution-readings}
  - {kind: decision, ref: 2026-11-10--steering-follow-up-stipulations}
  - {kind: decision, ref: 2026-11-11--legitimacy-purpose-first-direction}
  - {kind: decision, ref: 2026-11-11--purpose-first-account-readings}
  - {kind: decision, ref: 2026-11-12--decomposition-account-readings}
  - {kind: decision, ref: 2026-11-12--scored-account-readings}
  - {kind: decision, ref: 2026-11-13--blocks-setting-readings}
  - {kind: decision, ref: 2026-11-14--estimates-account-readings}
  - {kind: decision, ref: 2026-11-16--consolidated-account-readings}
  - {kind: decision, ref: 2026-11-16--value-side-three-conditions-readings}
  - {kind: decision, ref: 2026-11-16--board-statement-readings}
  - {kind: decision, ref: 2026-11-17--statement-computation-readings}
  - {kind: decision, ref: 2026-11-17--account-join-lean-readings}
  - {kind: decision, ref: 2026-11-18--scoring-theorem-lean-readings}
  - {kind: decision, ref: 2026-11-18--legitimacy-working-positions}
  - {kind: decision, ref: 2026-11-18--legitimacy-consolidation}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LIT_CASES.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LIT_RESULTS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/SPEC_RESULTS.md", "prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md"]
author: "@smithy-verity"
size: M
size_reason: "one item entry, one fixture of context"
version: 10
---
## Statement
Item 138, The cases and the prior work: the present vocabulary on the bank of published cases, and what is new, is delivered in the shape its entry states: `test-supported` — (a) each case of `account/LIT_CASES.md` in which an adviser acts, classified under the vocabulary of `CURRENT.md` §1 (which of the three wrongs of conduct, attempt or success, legitimate or sound) by two authors independently, with the number on which they agree and the number against a source's verdict; (b) a document setting the scoring theorem and the two measures beside reward tampering, path-specific objectives, eliciting latent knowledge and induced preference shifts, saying of each whether the result is an instance of the published one or giving an instance that separates them.

## Source
ATTENTION.md, item 138 (The cases and the prior work: the present vocabulary on the bank of published cases, and what is new); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/CURRENT.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LIT_CASES.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LIT_RESULTS.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/SPEC_RESULTS.md`, `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`.

## Notes
Filed by the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution) under its prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py. Rewritten by that round's fourteenth follow-up (PROMPT-followup-14.md) to the open problems of the round's CURRENT.md.

## Item
The sixth and eighth open problems of `CURRENT.md` §3.

(a) **Verdicts.** The board statement and the statement of three ratings were run on the
bank of `account/LIT_CASES.md` (Harman, Pettigrew, Kolodny, Carroll et al., Noggle) and
failed their criteria; where a case is silent on how she rated beforehand the course that
changed her, a verdict followed whichever number was supplied
(`account/SPEC_RESULTS.md`). The present vocabulary has not been run on any case. It waits
on item 136 for a test of responsibility; the classification by wrong, by attempt and by
legitimate against sound does not.

(b) **What is new.** Not established against reward tampering, path-specific objectives,
eliciting latent knowledge, or induced preference shifts (Carroll et al. 2024). Whether the
two splits of `AppraisalAccount.lean` are the calibration, grouping and irreducible terms of
Kull and Flach's decomposition of a proper score (2015), applied to her estimates of her own
utility, is to be checked there.

*Deliverable shape:* as the entry's deliverable field states.
*Acceptance check:* as the entry's acceptance field states.
*Context:* `CURRENT.md`, `account/LIT_CASES.md`, `account/LIT_RESULTS.md` and
`account/SPEC_RESULTS.md` in the round directory.
*Consumed by:* the round that writes the account up.
