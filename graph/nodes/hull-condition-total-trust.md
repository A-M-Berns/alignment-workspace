---
id: hull-condition-total-trust
kind: leaf
leaf_kind: step
action: Prove finite-dimensional Minkowski-Weyl (or finitely generated Farkas) in Lean once and close Hull.hullCondition_of_defers.
who: agent
files: [projects/deference/faf-cleanroom-2026-10-02/packages/corr-three-step-facts]
work:
  - {kind: open, ref: Hull.hullCondition_of_defers}
author: "@smithy-verity"
size: M
size_reason: one open declaration and one classical theorem
version: 1
---
## Statement
The hull condition is necessary and sufficient for question-relative Total
Trust under a common prior on a finite frame, the finite-frame form of Theorem
4.1 of Deference Done Better.

## Source
projects/deference/faf-cleanroom-2026-10-02/packages/corr-three-step-facts, the
open declaration Hull.hullCondition_of_defers.

## Notes
A plan root of the legitimacy-detection frame: the one named Lean gap whose
closing is reusable across the clean-room (shared with li-trust).
