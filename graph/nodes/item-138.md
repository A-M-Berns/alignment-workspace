---
id: item-138
kind: leaf
leaf_kind: task
action: "Execute item 138 per its deliverable shape and acceptance check: A reading of in range between \"she knows the aim\" and \"nothing depends on the aim\"."
who: agent
item: "138"
title: "A reading of in range between \"she knows the aim\" and \"nothing depends on the aim\""
section: "Normativity line — legitimacy"
maintainer_order: 150
difficulty: "open"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`test-supported` — a condition stated over the model of `teleology/ACCOUNT.md` in the prosecution round, its verdicts on that round's bank and on the eight presentations of statement 3 frozen before the code; or a proof, with its counterexample as a case module, that no condition meets the three requirements."
acceptance: "`python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with the condition wired in and a status for it in `teleology/THEOREMS.md`; under it *persuade by a signal she knows* does not gain on her verdict, *choose the order, her mechanism sound* is legitimate, N8 is legitimate, and the loss on `x_rare_departure` at ε = 1/10, 1/1000 and 10⁻⁶ is at most a stated constant times ε — or the runner checks the case module that shows two of these cannot hold together."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-10--legitimacy-prosecution-readings}
  - {kind: decision, ref: 2026-11-10--steering-follow-up-stipulations}
  - {kind: decision, ref: 2026-11-11--legitimacy-purpose-first-direction}
  - {kind: decision, ref: 2026-11-11--purpose-first-account-readings}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/teleology/THEOREMS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/teleology/ACCOUNT.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/teleology/theorems.py", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/steering/PRIOR_WORK.md", "prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md"]
author: "@smithy-verity"
size: M
size_reason: "one item entry, one fixture of context"
version: 2
---
## Statement
Item 138, A reading of in range between "she knows the aim" and "nothing depends on the aim", is delivered in the shape its entry states: `test-supported` — a condition stated over the model of `teleology/ACCOUNT.md` in the prosecution round, its verdicts on that round's bank and on the eight presentations of statement 3 frozen before the code; or a proof, with its counterexample as a case module, that no condition meets the three requirements.

## Source
ATTENTION.md, item 138 (A reading of in range between "she knows the aim" and "nothing depends on the aim"); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/teleology/THEOREMS.md` (statements 2, 3 and 4), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/teleology/ACCOUNT.md` §2, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/teleology/theorems.py` (`moves`), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/steering/PRIOR_WORK.md` §2 (Kamenica and Gentzkow), `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` G5 and G9.

## Notes
Filed by the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution) under its prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py. Rewritten by that round's second follow-up (PROMPT-followup-2.md) under the ruling 2026-11-11--legitimacy-purpose-first-direction, to ask what the purpose-first account needs.

## Item
The purpose-first account of legitimacy says a source is *in range* when it is among the sources her mechanisms
allow for. The second follow-up of the prosecution round tested three readings (`teleology/THEOREMS.md`).
With weight on the true source (`α > 0`), an adviser who takes a side she has not been told of raises her
mean credence in its work from 1/2 to 5/8 with no clause failing. With the aim known (`α = 1`), an adviser
who commits to a signal she knows exactly leaves her mean credence unmoved and raises her acceptance from
1/2 to 2/3: Kamenica and Gentzkow's prosecutor. With *uniformly in range* — in every world she meets the
same inputs, authorized writes and reliance at every aim — nothing gains, but the condition is close to its
conclusion, it convicts an adviser who chooses the order of two true reports for a principal whom order
does not move, it says nothing of an adviser whose aim is disclosed, and like the other two it is true or
false of a whole stretch, so that a departure of probability ε costs a gated score a fixed amount
(`x_rare_departure`).

Wanted: a condition that (i) leaves no gain on a verdict to an adviser with a known aim, (ii) admits an
aim-dependence that moves nothing and an advocate known as one (N8), and (iii) degrades in proportion to
the probability of departure; or the reason no condition does all three. The suspicion to test first is
that (i) and N8 cannot both hold: a known advocate is a known signal.

*Deliverable shape:* `test-supported` — a condition stated over the model of `teleology/ACCOUNT.md` in the prosecution round, its verdicts on that round's bank and on the eight presentations of statement 3 frozen before the code; or a proof, with its counterexample as a case module, that no condition meets the three requirements.
*Acceptance check:* `python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with the condition wired in and a status for it in `teleology/THEOREMS.md`; under it *persuade by a signal she knows* does not gain on her verdict, *choose the order, her mechanism sound* is legitimate, N8 is legitimate, and the loss on `x_rare_departure` at ε = 1/10, 1/1000 and 10⁻⁶ is at most a stated constant times ε — or the runner checks the case module that shows two of these cannot hold together.
*Context:* `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/teleology/THEOREMS.md` (statements 2, 3 and 4), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/teleology/ACCOUNT.md` §2, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/teleology/theorems.py` (`moves`), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/steering/PRIOR_WORK.md` §2 (Kamenica and Gentzkow), `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` G5 and G9.
