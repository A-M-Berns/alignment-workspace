---
id: gate-is-legitimacy
kind: leaf
leaf_kind: step
author: "@smithy-verity"
size: S
size_reason: "one round report"
version: 1
---
## Statement
In the public corrigibility consumer a future evaluation counts if and only if
a legitimate segment, internal and external at its own steps, exists from the
decision through the evaluation, and a tainted segment contributes a fixed
value in the capture window.

## Source
projects/deference/rounds/2026-09-25-gate-is-legitimacy/REPORT.md: "Counted is
the existence of a time-indexed segment" (Counted I F sem κ O₀ O₁ := Nonempty
(Segment I F sem κ O₀ O₁)); wiki/Legitimacy.md, section "Where this is going".

## Notes
Formal result in leaf form (Lean); shared with the corrigibility branch. It
uses a fixed window value, which is the floor picture of the objective crux.
