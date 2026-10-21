---
id: comparison-theorem-under-relational-index-maps
kind: leaf
leaf_kind: question
given: permissive-morphisms-wanted
action: "Attempt Theorem 4.15 and Theorem 5.8 under the relational morphism, and on failure produce the smallest finite counterexample as a Python table in the clean-room style."
who: agent
author: "@smithy-verity-opus55"
size: M
size_reason: "two theorems to re-prove under a new morphism"
version: 1
---
## Statement
Eisenstat's exact and approximate correspondence theorems remain true when the
index map from target to source variables is replaced by a relation, with each
component map reading all related sources.

## Source
projects/deference/faf-cleanroom-2026-10-02/packages/udt-condense-dd/udt-condense-dd-findings.md,
The Eisenstat map (Theorem 4.15, Theorem 5.8; `RVModel.Hom` in
`Morphism.lean`).

## Notes
The statement whose truth settles the relational candidate.
