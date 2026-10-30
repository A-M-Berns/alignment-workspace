---
id: item-1
kind: leaf
leaf_kind: task
action: "Execute item 1 per its deliverable shape and acceptance check: Persistence of the certified core minimum."
who: agent
item: "1"
title: "Persistence of the certified core minimum"
section: "Normativity line"
maintainer_order: 5
difficulty: "open"
project: normativity
dispatchable: true
item_status: open
deliverable: "`lean-proved` in `Workspace.Normativity.Contrib`, or `witness-checked` for the negative direction."
acceptance: "The Lean gate builds and audits clean; or the `witness` checker accepts the trajectory with the `violates-at-least-one` property."
context: ["projects/normativity/consolidation-aug9/THEORY_11_SETTLEMENT_INTERFACE.md"]
work:
  - {kind: decision, ref: 2026-10-02--formalized-agent-foundations-pin-moves-repository}
author: "@smithy-verity"
size: M
size_reason: "one item entry of 136 words"
version: 1
---
## Statement
A solution to item 1 ships either a proof that a positive minimum persists under stated conditions, with necessity witnesses for those conditions; or a displayed trajectory driving it to zero under conditions the interface permits.

## Source
PRIORITIES.md, item 1 (Persistence of the certified core minimum); its context: `projects/normativity/consolidation-aug9/THEORY_11_SETTLEMENT_INTERFACE.md` §5.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
Containment of the core homothet is linear in the reference at fixed
coefficient, so whether a declared core minimum is satisfiable *at a date* is one
linear program (`NL-SI-A2`, `NL-SI-A3`). What is open is the infimum over dates:
whether a declared minimum keeps being satisfiable as settlement contracts the
region. `NL-SI-A4` shows no finite family of per-date checks decides it, and
`NL-SI-A7` shows both outcomes occur on small instances.

*Deliverable shape:* `lean-proved` in `Workspace.Normativity.Contrib`, or `witness-checked` for the negative direction.
*Acceptance check:* The Lean gate builds and audits clean; or the `witness` checker accepts the trajectory with the `violates-at-least-one` property.

*Context:* `projects/normativity/consolidation-aug9/THEORY_11_SETTLEMENT_INTERFACE.md` §5.
*A solution ships:* either a proof that a positive minimum persists under stated
conditions, with necessity witnesses for those conditions; or a displayed
trajectory driving it to zero under conditions the interface permits.
