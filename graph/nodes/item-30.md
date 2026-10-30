---
id: item-30
kind: leaf
leaf_kind: task
action: "Execute item 30 per its deliverable shape and acceptance check: A learner with sublinear Φ_law-regret, and what it retires."
who: agent
item: "30"
title: "A learner with sublinear Φ_law-regret, and what it retires"
section: "Normativity line — the learning track"
maintainer_order: 12
difficulty: "partially closed: learning-positive, integration-blocked"
project: normativity
dispatchable: true
item_status: open
deliverable: "`enumeration-verified` over the declared finite environment at the four declared horizons, or `lean-proved` for the bound; the consequence as `lean-proved` with an inhabitation witness."
acceptance: "`python3 -m checkers.run` accepts the registered entry; or the `lean` gate is green."
context: ["projects/normativity/rounds/2026-08-11-phi-regret-learner/"]
author: "@smithy-verity"
size: L
size_reason: "one item entry of 511 words"
version: 1
---
## Statement
A solution to item 30 ships the bound or its absence, at each horizon, against the declared class; and an honest statement of whether the successful learner is still answerable and inside its declared service work, which the spec calls S4 and expects to be where the round spends its time.

## Source
PRIORITIES.md, item 30 (A learner with sublinear Φ_law-regret, and what it retires); its context: `PHI_REGRET_TEST_SPEC.md` §§1–6 fixes the environment, the three baselines, the measured quantities and the order of work; `projects/normativity/rounds/2026-08-11-phi-regret-learner/` is the controlling item-30 result.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
The controlling question of the track.

> Given the frozen finite comparator and replay environment, determine whether a
> specified online learner achieves sublinear Φ_law-regret, and whether that
> guarantee implies retirement of every positive-rate uniformly remediable
> failure pattern.

Both halves. The expected-loss consequence is one line given the first — total
mixed-action mass `Ω(T)` on source labels with a fixed admitted repair saving
`δ > 0` forces `R_T(φ) ≥ ρδT − B`. A density claim about one sampled path needs
an additional sampling argument. The content is entirely in the hypotheses,
three of which the environment supplies and one of which is the bound.

Use the fixed labels and nine programs in
`projects/normativity/rounds/2026-08-11-phi-regret-bridge/`. Implement
Blum--Mansour Theorem 18's row-conditioned weights over eight source labels and
nine programs, and its stationary distribution. Measure expected mixed-action
charge first. Use the `sqrt(8 log 9)` dependence; do not use plain exponential
weights over nine transformations or report a `sqrt(log 9)` bound. A sampled
trajectory requires a separately stated sampling result. Report whether the
implementation is horizon-tuned or supplies a proved anytime schedule.
If it retains the workspace's exact-rational execution discipline, also state
how the source's optimized real parameter and stationary distribution are
represented without silently changing the bound.

*Result:* `projects/normativity/rounds/2026-08-11-phi-regret-learner/` implements
the Theorem 18 construction with 8 source rows and 9 program weights per row,
the transformation-weighted matrix, a deterministic exact stationary selector
for the represented numerical weights, and the source row update. The real
exponential update uses controlled `Decimal` arithmetic; transition and
stationarity calculations are exact for those finite decimal weights. Declared
experiments show decreasing maximum regret per round on the adversarial
impediment fixture, and the cited theorem plus the item-29 bridge supplies the
expected mixed-loss guarantee. The recurrent-failure consequence therefore
retires positive asymptotic expected mass on represented uniformly saving
repairs.

The learning computation is not yet integrated into the bounded answerability
architecture. Sampled canonical responses produce faithful, non-erasing,
response-service-feasible records, but `ServiceCosts` has no coordinate for the
72 weight updates or stationary solve, and the learner state is not recorded as
an answerable artifact. Item 30 remains open only on that explicit integration
interface. Also open: sampled-path and anytime guarantees, exact-real executable
identity, and comparator coverage beyond the weak nine-program class.

**Report `|Φ_law|` and its contents alongside any regret number.** Sublinear
regret against a nine-element class is a weak statement, and a report without the
class is not a result.

*Deliverable shape:* `enumeration-verified` over the declared finite environment
at the four declared horizons, or `lean-proved` for the bound; the consequence as
`lean-proved` with an inhabitation witness.
*Acceptance check:* `python3 -m checkers.run` accepts the registered entry; or the
`lean` gate is green.
*Context:* `PHI_REGRET_TEST_SPEC.md` §§1–6 fixes the environment, the three
baselines, the measured quantities and the order of work;
`projects/normativity/rounds/2026-08-11-phi-regret-learner/` is the controlling
item-30 result.
*A solution ships:* the bound or its absence, at each horizon, against the
declared class; and an honest statement of whether the successful learner is
still answerable and inside its declared service work, which the spec calls S4
and expects to be where the round spends its time.
