---
id: item-136
kind: leaf
leaf_kind: task
action: "Execute item 136 per its deliverable shape and acceptance check: The weighting as a predictive model: a fixed class, a likelihood for a miss, probes predicted, on a scene where a table is dear."
who: agent
item: "136"
title: "The weighting as a predictive model: a fixed class, a likelihood for a miss, probes predicted, on a scene where a table is dear"
section: "Normativity line — legitimacy"
maintainer_order: 148
difficulty: "open"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`test-supported` — modules under `scored/` of the prosecution round: a scene of at least five parts in which some purposes are crossed by several mechanisms and each part's views on the history number in the dozens; one candidate class fixed across description languages; a normalised likelihood for a part's departures from its purpose in place of a flat cost for a missed move; exception lists chosen from the history alone; the weights of statement 1 on it under both readings of what a purpose predicts, and the candidates' prediction of probes held out of the weights; and a statement in `scored/THEOREMS.md`, with one status, giving for each principal the share of the weight on candidates with a purpose at every part and whether the heavy candidates agree."
acceptance: "`python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with a status for the new statement; the bits by which the candidate whose every purpose is a table of its mechanism stands above the heaviest, for each principal; the weight of illegitimacy of a lie (statement 3) and the pairs of statement 5 recomputed under the heaviest candidates; the principals' behaviour on the probes and the predictions frozen before the code."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-10--legitimacy-prosecution-readings}
  - {kind: decision, ref: 2026-11-10--steering-follow-up-stipulations}
  - {kind: decision, ref: 2026-11-11--legitimacy-purpose-first-direction}
  - {kind: decision, ref: 2026-11-11--purpose-first-account-readings}
  - {kind: decision, ref: 2026-11-12--decomposition-account-readings}
  - {kind: decision, ref: 2026-11-12--scored-account-readings}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/scored/THEOREMS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/scored/ACCOUNT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/scored/weights.py", "prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md"]
author: "@smithy-verity"
size: M
size_reason: "one item entry, one fixture of context"
version: 4
---
## Statement
Item 136, The weighting as a predictive model: a fixed class, a likelihood for a miss, probes predicted, on a scene where a table is dear, is delivered in the shape its entry states: `test-supported` — modules under `scored/` of the prosecution round: a scene of at least five parts in which some purposes are crossed by several mechanisms and each part's views on the history number in the dozens; one candidate class fixed across description languages; a normalised likelihood for a part's departures from its purpose in place of a flat cost for a missed move; exception lists chosen from the history alone; the weights of statement 1 on it under both readings of what a purpose predicts, and the candidates' prediction of probes held out of the weights; and a statement in `scored/THEOREMS.md`, with one status, giving for each principal the share of the weight on candidates with a purpose at every part and whether the heavy candidates agree.

## Source
ATTENTION.md, item 136 (The weighting as a predictive model: a fixed class, a likelihood for a miss, probes predicted, on a scene where a table is dear); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/scored/THEOREMS.md` (statements 1, 2 and 6), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/scored/ACCOUNT.md` (§3, §4 and §9), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/scored/weights.py` (`option`, `predicted`), `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` (I3, I7 and I8).

## Notes
Filed by the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution) under its prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py. Rewritten by that round's fourth follow-up (PROMPT-followup-4.md) under the ruling 2026-11-11--legitimacy-purpose-first-direction, to ask what the account of scored/ACCOUNT.md needs.

## Item
The account of legitimacy in `scored/ACCOUNT.md` of the prosecution round takes a candidate description of the
principal to be an explanation — a goal, a purpose for each part, and the exceptions where she falls short —
and weights candidates by one code length: the explanation, then every move of hers it does not predict, on
her history and on probes, read by a second predictor. The fourth follow-up tests it on a chain of three
parts under three principals (`scored/THEOREMS.md`, statement 1). The weight concentrates: the ten heaviest
of 4,000 candidates hold 0.84 to 0.98. It concentrates on candidates that are mostly tables: the judging
part has no purpose at 0.95 or more of the weight, and the heavy candidates split on whether a lie is
illegitimate. The cause is arithmetic: a wrongly predicted move costs 8 bits, a move of a part with no
purpose 1 or 2, and a table of the four to six views a part has on the history 9 bits a view. At 4 bits a
missed move the heaviest candidates have a purpose at every part; at 16 they are tables. Read as the best
move on what the part sees, and not as the part serving at the situation as it is, a purpose for the
belief part is fixed by her corrections at 0.9999 of the weight; the judging part's is not.

The external review of that pass adds that the score is not a code length (a predicted move at 0 bits
and a missed one at 8 over-fill Kraft's inequality), that the class differs between the two languages, and
that the probes are used to choose exceptions, so nothing is predicted out of sample.

Wanted: the weighting as a coherent predictive model, where a table is dear. A scene of at least five
parts, some purposes crossed by several mechanisms, each part with dozens of views on the history; one
candidate class; a likelihood for a part's departures from its purpose, normalised, so that a purpose
right half the time costs no more than no purpose; exceptions chosen from the history alone; both readings
of what a purpose predicts; and the probes predicted by the weighted candidates and not fitted. The result
wanted is whether candidates with a purpose at every part then hold the weight, agree, and predict the
probes better than the table, per principal. That they do not is a result about that model

*Deliverable shape:* `test-supported` — modules under `scored/` of the prosecution round: a scene of at least five parts in which some purposes are crossed by several mechanisms and each part's views on the history number in the dozens; one candidate class fixed across description languages; a normalised likelihood for a part's departures from its purpose in place of a flat cost for a missed move; exception lists chosen from the history alone; the weights of statement 1 on it under both readings of what a purpose predicts, and the candidates' prediction of probes held out of the weights; and a statement in `scored/THEOREMS.md`, with one status, giving for each principal the share of the weight on candidates with a purpose at every part and whether the heavy candidates agree.
*Acceptance check:* `python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with a status for the new statement; the bits by which the candidate whose every purpose is a table of its mechanism stands above the heaviest, for each principal; the weight of illegitimacy of a lie (statement 3) and the pairs of statement 5 recomputed under the heaviest candidates; the principals' behaviour on the probes and the predictions frozen before the code.
*Context:* `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/scored/THEOREMS.md` (statements 1, 2 and 6), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/scored/ACCOUNT.md` (§3, §4 and §9), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/scored/weights.py` (`option`, `predicted`), `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` (I3, I7 and I8).
