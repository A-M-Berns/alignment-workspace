---
id: item-49
kind: leaf
leaf_kind: task
action: "Execute item 49 per its deliverable shape and acceptance check: A kernel proof of `DistanceComplete` for the exact dual-distance family."
who: agent
item: "49"
title: "A kernel proof of `DistanceComplete` for the exact dual-distance family"
section: "Normativity line — traderized enforcement"
maintainer_order: 27
difficulty: "substantial"
project: normativity
dispatchable: true
item_status: open
deliverable: "`lean-proved`, discharging the `DistanceComplete` hypothesis of `exists_credence_of_contract` at the exact dual-distance family."
acceptance: "the Lean gate is green, the axiom audit is clean, and the composition typechecks with no `DistanceComplete` argument supplied by the caller."
context: ["projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md"]
author: "@smithy-verity"
size: M
size_reason: "one item entry of 206 words"
version: 1
---
## Statement
Item 49, A kernel proof of `DistanceComplete` for the exact dual-distance family, is delivered in the shape its entry states: `lean-proved`, discharging the `DistanceComplete` hypothesis of `exists_credence_of_contract` at the exact dual-distance family.

## Source
PRIORITIES.md, item 49 (A kernel proof of `DistanceComplete` for the exact dual-distance family); its context: `projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md` §C, debt 1; `.../2026-08-16-traderized-enforcement/PROOF_CLOSURE.md` §V.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
The exactness half of intrinsic conformance: from conformance on the exact
dual-distance rows, produce an admissible mixture within `δ`. This is convex
duality for a finite rational polytope — equivalently a finite minimax theorem.
Mathlib carries neither a von Neumann minimax theorem nor a convenient
`ℓ^∞`/`ℓ¹` separation over `Fin d → ℝ`, so the work is either proving the duality
directly through `geometric_hahn_banach_point_closed` — which needs
`f x = Σ_i c_i x_i` from the finite basis, `sup_{‖y‖_∞ ≤ 1}⟪c,y⟫ = ‖c‖₁`, and
closedness of `K + δ'B_∞` — or proving a finite minimax theorem and specializing.

The interface is already in place and cannot be met vacuously:
`CoherenceModulus.DistanceComplete`, `gap_le_of_distanceComplete`, and the
composition `IntrinsicCoherence.exists_credence_of_contract` waiting on it. The
statement is currently `derived` plus exhaustive verification over stated
rational grids in `projects/normativity/rounds/2026-08-16-traderized-enforcement/tests/test_coherence.py`, against an
independently computed
distance.

*Deliverable shape:* `lean-proved`, discharging the `DistanceComplete` hypothesis
of `exists_credence_of_contract` at the exact dual-distance family.
*Acceptance check:* the Lean gate is green, the axiom audit is clean, and the
composition typechecks with no `DistanceComplete` argument supplied by the
caller.
*Context:* `projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md` §C, debt
1; `.../2026-08-16-traderized-enforcement/PROOF_CLOSURE.md` §V.
*Why it is [substantial] rather than [open]:* the statement is known, the route is
named twice over, and the obstruction is Mathlib coverage rather than
mathematics.
