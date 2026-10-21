---
id: uea-rosi-lift
kind: leaf
leaf_kind: route
given: uea-floored-agent-theorem@valid
action: "Type the rOSI statements of Theorem 1 and of Theorems B and C with discounting explicit, and mark which finite-shadow steps use finiteness."
who: agent
author: "@smithy-verity-opus55"
size: M
size_reason: "a statement to type and two proof steps to locate"
version: 1
---
## Statement
Theorems B and C of the finite sequential self-game hold in the
reflective-oracle Solomonoff setting with an infinite discounted horizon, with
the posterior w_h read as the self-hypothesis's weight.

## Source
projects/deference/faf-cleanroom-2026-10-02/DIGEST.md.

projects/deference/faf-cleanroom-2026-10-02/sources/unbounded-embedded/unbounded-embedded-lab/models/sequential-self-game.md.

## Notes
A route of uea-floored-agent-theorem.improvable. The digest records that the
rOSI statement is typed nowhere in the run, so the action first types it, with
discounting explicit (the trap chain refutes a horizon-free δ at γ = 1), then
marks the finite-shadow steps that use finiteness (the Kakutani existence
step, the path-measure unrolling).
