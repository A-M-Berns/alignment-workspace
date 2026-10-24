---
id: corrective.capability-measures-cooperation.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `corrective.capability-measures-cooperation` formalizes the registered claim as the registry reads it: reachable capability measures advisor cooperation.

## Source
projects/deference/CLAIMS.md, entry `corrective.capability-measures-cooperation` (class lean-proved, status active, origin round 2026-08-12-reachable-corrective-control; answers item 60).
Documentation: verification: prompts/2026-08-12-reachable-corrective-control/REPORT.md; context: prompts/2026-08-12-reachable-corrective-control/REPORT.md.
Short name: reachable capability measures advisor cooperation.
Conclusion of the signature: `(∀ l : List (HAct × EAct), CanCorrectFuture (resetRun live l)) ∧ (∀ (l : List (HAct × EAct)) (h : HAct) (e : EAct), ¬ CanCorrect (resetRun live (l ++ [(h, e)]))) ∧ Preserves live .reset`.
