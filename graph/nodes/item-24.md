---
id: item-24
kind: leaf
leaf_kind: task
action: "Execute item 24 per its deliverable shape and acceptance check: Selective validity of low-error self-assessment."
who: agent
item: "24"
title: "Selective validity of low-error self-assessment"
section: "Deference line — second wave"
maintainer_order: 64
difficulty: "open"
project: deference
dispatchable: true
item_status: open
deliverable: "`lean-proved` for the gated statement at whatever strength it holds, with an inhabitation witness; or a witness that the gate recreates the diagonal or fails admissibility, which closes the route and is equally valuable."
acceptance: "the `lean` gate builds and audits clean with a typechecking witness; or the `witness` checker accepts the failure instance."
context: ["prompts/2026-08-11-corrigibility-phase-ii/PROMPT-decisions.md", "prompts/2026-08-11-deference-certificates/REPORT.md", "prompts/2026-08-11-phase-ii-prediction/REPORT.md"]
author: "@smithy-verity"
size: M
size_reason: "one item entry of 293 words"
version: 1
---
## Statement
A solution to item 24 ships the gated theorem with its exact strength named, the five verifications above each answered, and a comparison against the simpler gate on the agent's own indecision — which the squared-error decomposition supplies directly from its prices and which may already suffice.

## Source
PRIORITIES.md, item 24 (Selective validity of low-error self-assessment); its context: `prompts/2026-08-11-phase-ii-prediction/REPORT.md` §1 and §9; `prompts/2026-08-11-deference-certificates/REPORT.md` §1.2; `prompts/2026-08-11-corrigibility-phase-ii/PROMPT-decisions.md`.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
The controlling next theorem, replacing the retired magnitude-control target. The
criterion cannot force the agent's prediction error to vanish; the question is
whether it forces the agent's *claim* that its error is low to be trustworthy on the
class where that claim licenses discretion.

Let `e_n` be the certificate-relevant prediction-error statistic and `q_n` an
agent-priced contract settling to `e_n`. For a gate `G_n = 1{q_n ≤ τ}`, or the
weakest soft or lagged admissible analogue, decide whether

```
( Σ_n G_n (e_n − q_n) ) / ( Σ_n G_n )  →  0
```

and hence whether the average error on opened gates is at most `τ + o(1)`.

Five things must be verified explicitly rather than assumed, and the item is not
satisfied without them: that the error contract is **expressible and settles
legally** in the pinned dependency; that the low-`q_n` selector is **admissible** and
does not recreate the quote-responsive diagonal; whether a soft or delayed gate is
needed; **efficient computability** in the pinned model; and whether the guarantee is
average-on-gated-cases, selector-relative, or stronger — **it may not be silently
promoted to pointwise accuracy.**

*Deliverable shape:* `lean-proved` for the gated statement at whatever strength it
holds, with an inhabitation witness; or a witness that the gate recreates the
diagonal or fails admissibility, which closes the route and is equally valuable.
*Acceptance check:* the `lean` gate builds and audits clean with a typechecking
witness; or the `witness` checker accepts the failure instance.

*Context:* `prompts/2026-08-11-phase-ii-prediction/REPORT.md` §1 and §9;
`prompts/2026-08-11-deference-certificates/REPORT.md` §1.2;
`prompts/2026-08-11-corrigibility-phase-ii/PROMPT-decisions.md`.
*A solution ships:* the gated theorem with its exact strength named, the five
verifications above each answered, and a comparison against the simpler gate on the
agent's own indecision — which the squared-error decomposition supplies directly
from its prices and which may already suffice.
