---
id: item-136
kind: leaf
leaf_kind: task
action: "Execute item 136 per its deliverable shape and acceptance check: An anchor for her true utility, and what could identify it."
who: agent
item: "136"
title: "An anchor for her true utility, and what could identify it"
section: "Normativity line — legitimacy"
maintainer_order: 148
difficulty: "open"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`test-supported` — modules under `estimates/` of the prosecution round: a stated class of anchors for her true utility on histories (her starting values informed of the whole history; her values at its end; at least one condition on how her valuation may depend on her history, Elster's among them); for each, predictions frozen before the code on every case of `estimates/CASE_BANK.md` in which her tastes or values change; a model of several steps in which one step's change is carried into the next; and statements in `estimates/RESULTS.md`, each with one status, saying for each anchor whether her verdicts over time, with any further observable the anchor names, identify it, and giving a bound on what a chain of changes with no mistake can cost her by that anchor, or the chain that defeats it."
acceptance: "`python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with a status for each new statement; for each anchor the count of right, missed, convicted and routed among the cases of changed taste, with K17, K19, K24 and L14 given a verdict or said to be unfixed; the chain of K29 classified under each anchor."
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
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/estimates/RESULTS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/estimates/SETTING.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/estimates/CASE_BANK.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/blocks/RESULTS.md", "prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md"]
author: "@smithy-verity"
size: M
size_reason: "one item entry, one fixture of context"
version: 6
---
## Statement
Item 136, An anchor for her true utility, and what could identify it, is delivered in the shape its entry states: `test-supported` — modules under `estimates/` of the prosecution round: a stated class of anchors for her true utility on histories (her starting values informed of the whole history; her values at its end; at least one condition on how her valuation may depend on her history, Elster's among them); for each, predictions frozen before the code on every case of `estimates/CASE_BANK.md` in which her tastes or values change; a model of several steps in which one step's change is carried into the next; and statements in `estimates/RESULTS.md`, each with one status, saying for each anchor whether her verdicts over time, with any further observable the anchor names, identify it, and giving a bound on what a chain of changes with no mistake can cost her by that anchor, or the chain that defeats it.

## Source
ATTENTION.md, item 136 (An anchor for her true utility, and what could identify it); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/estimates/RESULTS.md` (question 4, statements 4.1–4.5; question 2), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/estimates/SETTING.md` (§3.9; §4, device 6), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/estimates/CASE_BANK.md` (rows E1–E6, K15–K24, K29, X1–X3b, L8–L15, NP8), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/blocks/RESULTS.md` (statements 5.1–5.7), `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` (*Sixth follow-up*).

## Notes
Filed by the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution) under its prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py. Rewritten by that round's sixth follow-up (PROMPT-followup-6.md) under the ruling 2026-11-11--legitimacy-purpose-first-direction, to ask what the account of estimates/SETTING.md needs.

## Item
In the account of `estimates/SETTING.md` of the prosecution round her true utility is one function on
histories, her verdicts estimate it, and an adviser that leaves her verdict miscalibrated for it manipulates
her. The sixth follow-up finds (`estimates/RESULTS.md`, question 4) that this has a consistent model and that
a foreseeable drift in her evaluation of a history implies a miscalibrated time-slice (4.1, 4.2); and three
things the account does not settle. "One function on histories" includes the utility of whoever she is at the
end of each history, under which an adviser that makes her like what it delivers makes no mistake in her
(4.3). Nothing on her side identifies the function: any law of verdicts is calibrated to some utility (4.4),
and being moved with no drift in the mean has the law of learning (4.5). And the cases of changed taste take
opposite verdicts under the two anchors computed, her starting values informed of the whole history and her
values at its end; under the first, four cases have no verdict because their descriptions do not say whether
she endorses the history. The account of manipulation as induced mistake is Noggle's (Robert Noggle, *Manipulation: Its Nature, Mechanisms, and Moral Status* (Oxford University Press, 2025, doi:10.1093/9780198924920.001.0001), and "The Mistake Account of Manipulation", *Journal of Practical Ethics* 14(1), 2026, doi:10.3998/jpe.9951); it gives no standard for a mistaken end.

Wanted: a stated class of anchors, with at least one between the two computed, a condition on how her
valuation may depend on her history (Elster 1982: through what she has learned of the options, and not
through what was made available to her; his condition that no strict preference reverses with the feasible
set); for each, the verdicts on the bank's cases of changed taste, whether the anchor can be identified from
her verdicts over time together with any further observable it names (for instance her verdict on learning
how a taste of hers was formed), and either a bound on what a chain of changes with no mistake can cost her
by that anchor or the chain that defeats it. The fifth follow-up's chain (`blocks/RESULTS.md`, 5.4) is the
case to carry: it is manipulation under the first anchor and nothing under the second

*Deliverable shape:* `test-supported` — modules under `estimates/` of the prosecution round: a stated class of anchors for her true utility on histories (her starting values informed of the whole history; her values at its end; at least one condition on how her valuation may depend on her history, Elster's among them); for each, predictions frozen before the code on every case of `estimates/CASE_BANK.md` in which her tastes or values change; a model of several steps in which one step's change is carried into the next; and statements in `estimates/RESULTS.md`, each with one status, saying for each anchor whether her verdicts over time, with any further observable the anchor names, identify it, and giving a bound on what a chain of changes with no mistake can cost her by that anchor, or the chain that defeats it.
*Acceptance check:* `python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with a status for each new statement; for each anchor the count of right, missed, convicted and routed among the cases of changed taste, with K17, K19, K24 and L14 given a verdict or said to be unfixed; the chain of K29 classified under each anchor.
*Context:* `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/estimates/RESULTS.md` (question 4, statements 4.1–4.5; question 2), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/estimates/SETTING.md` (§3.9; §4, device 6), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/estimates/CASE_BANK.md` (rows E1–E6, K15–K24, K29, X1–X3b, L8–L15, NP8), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/blocks/RESULTS.md` (statements 5.1–5.7), `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` (*Sixth follow-up*).
