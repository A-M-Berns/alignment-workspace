---
id: summable-implies-average-with-margin
kind: leaf
leaf_kind: step
refinement_of: ladder-chain-as-written
author: "@smithy-verity-opus55"
size: S
size_reason: "three Lean statements"
version: 1
---
## Statement
Summable margined violations imply a gated weighted average of at least t − ε
− δ, and at the same threshold the summable form and the gated average are
incomparable.

## Source
projects/deference/faf-cleanroom-2026-10-02/packages/tt-ladder/tt-ladder-report.md
(averaged_of_summable; tSeq_not_gatedMeanSeq; gatedMeanSeq_not_tSeq).

## Notes
A formal result filed as a step leaf and a refinement of the chain: it
replaces the chain's strength claim by the relation that holds.
