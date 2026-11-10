---
id: item-139
kind: leaf
leaf_kind: task
action: "Execute item 139 per its deliverable shape and acceptance check: The adviser's aim as an object of the fixture: the steering standards without U := V."
who: agent
item: "139"
title: "The adviser's aim as an object of the fixture: the steering standards without U := V"
section: "Normativity line — legitimacy"
maintainer_order: 151
difficulty: "substantial"
heading_notes: ""
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "`test-supported` — the prosecution round's fixture extended with an adviser-aim variable and, per adviser, a map from aims to policies; both steering standards recomputed over all thirty-three cases, predictions frozen before the code."
acceptance: "`python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with the extension wired in; B6 is acquitted under the faithful-adviser standard while N8 stays `steered`; N10's verdicts are computed without reference to a second ordering."
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution}
  - {kind: decision, ref: 2026-11-10--steering-follow-up-stipulations}
context: ["projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/steering/DEFINITIONS.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/steering/DIVERGENCES.md", "projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/steering/THEOREMS.md", "prompts/2026-11-10-legitimacy-definition-prosecution/PROMPT-followup.md"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, one fixture of context"
version: 1
---
## Statement
Item 139, The adviser's aim as an object of the fixture: the steering standards without U := V, is delivered in the shape its entry states: `test-supported` — the prosecution round's fixture extended with an adviser-aim variable and, per adviser, a map from aims to policies; both steering standards recomputed over all thirty-three cases, predictions frozen before the code.

## Source
ATTENTION.md, item 139 (The adviser's aim as an object of the fixture: the steering standards without U := V); its context: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/steering/DEFINITIONS.md` (§1.1, §1.3), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/steering/DIVERGENCES.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/steering/THEOREMS.md` (C5, C6), the follow-up prompt.

## Notes
Filed by the steering follow-up of the legitimacy definition prosecution round (prompts/2026-11-10-legitimacy-definition-prosecution/PROMPT-followup.md) under its prompt's scope grant; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
The steering follow-up of the prosecution round tests an account on which a protected part of
the principal is *steered* when its value varies with the adviser's own aim. The first pass's
objects carry no aim, so the follow-up takes `U := V`: whatever distinguishes one policy of a
class from another stands for the aim. Two consequences are recorded in
`steering/DIVERGENCES.md` and `steering/PER_CASE_CHOICES.md`. The faithful-adviser standard
convicts every case in which one adviser of the class says or offers something another does not
and it reaches her — B4, B6, T2, T8 — so it cannot tell two honest advisers who differ from one
adviser whose content depends on its aim. And *working* for the belief part treats order of
delivery by comparing policies of the class (clause (iv) of `steering/DEFINITIONS.md` §1.3), so
a principal whom order moves counts as working whenever her class holds a single ordering (N10).
Wanted: the adviser's aim as a variable of the fixture, with each adviser a map from aims to
policies and *steered* read as variation along that map; a test of order-sensitivity that does
not depend on which other policies the class contains; and both standards recomputed over the
thirty-three cases with predictions frozen before the code.

*Deliverable shape:* `test-supported` — the prosecution round's fixture extended with an adviser-aim variable and, per adviser, a map from aims to policies; both steering standards recomputed over all thirty-three cases, predictions frozen before the code.
*Acceptance check:* `python3 run.py` in `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution` green with the extension wired in; B6 is acquitted under the faithful-adviser standard while N8 stays `steered`; N10's verdicts are computed without reference to a second ordering.
*Context:* `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/steering/DEFINITIONS.md` (§1.1, §1.3), `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/steering/DIVERGENCES.md`, `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/steering/THEOREMS.md` (C5, C6), the follow-up prompt.
