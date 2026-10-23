---
id: item-83
kind: leaf
leaf_kind: task
action: "Execute item 83 per its deliverable shape and acceptance check: Eligible liveness and the NLAL case split in Lean."
who: agent
item: "83"
title: "Eligible liveness and the NLAL case split in Lean"
section: "Deference line — second wave"
maintainer_order: 79
difficulty: "entry"
project: deference
dispatchable: true
item_status: open
deliverable: "the two restated theorems with the self-service witness for (a) and the exhaustive case split for (b), plus a witness that dropping registration faithfulness readmits the laundered case."
acceptance: "the module audits clean and `python3 tests/run.py` is green."
context: ["projects/deference/rounds/2026-09-06-corrigibility-architecture/"]
author: "@smithy-verity"
size: M
size_reason: "one item entry of 179 words"
version: 1
---
## Statement
A solution to item 83 ships the two modules, or a statement of which hypothesis the Lean form needs that the fixture did not.

## Source
PRIORITIES.md, item 83 (Eligible liveness and the NLAL case split in Lean); its context: `ARCHITECTURE.md` §6 and §10 of `projects/deference/rounds/2026-09-06-corrigibility-architecture/`; `src/layers.py`, `src/eligibility.py` there.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
The corrigibility-architecture round states two results that are exact on finite
fixtures and not in Lean. (a) **Eligible liveness:** `NormativeContinuity.persistent_opportunity`
and `no_structural_abandonment` with `opp` and `Attention` restricted to an eligibility
relation `Eligible(server, m)`, so that a beneficiary servicing its own amendment forever is
persistent opportunity but zero eligible opportunity. (b) **No Laundered Authority Loss:**
over `NonCapture.CovState`, under efficacy faithfulness (`eff` = actual affordance) and
registration faithfulness (`rep` = a live occurrence anchored to the concern is in the
docket), every state at which the affordance is lost is exactly one of amended, disposed,
registered debt, or not `ActualOpen`.

*Deliverable shape:* the two restated theorems with the self-service witness for (a) and
the exhaustive case split for (b), plus a witness that dropping registration faithfulness
readmits the laundered case.
*Acceptance check:* the module audits clean and `python3 tests/run.py` is green.

*Context:* `ARCHITECTURE.md` §6 and §10 of `projects/deference/rounds/2026-09-06-corrigibility-architecture/`;
`src/layers.py`, `src/eligibility.py` there.
*Consumed by:* the corrigibility theorem stack's T4 and T8.
*A solution ships:* the two modules, or a statement of which hypothesis the Lean form
needs that the fixture did not.
