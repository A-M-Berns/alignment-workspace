---
id: compiler.deductive-end-to-end.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `compiler.deductive-end-to-end` formalizes the registered claim as the registry reads it: finite-date coherence with the original criterion, deductively.

## Source
projects/normativity/CLAIMS.md, entry `compiler.deductive-end-to-end` (class lean-proved, status active, origin round 2026-08-18-projection-enforcement; answers item 48).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-18-projection-enforcement/FINAL_FORMALIZATION_STATUS.md.
Short name: finite-date coherence with the original criterion, deductively.
Conclusion of the signature: `IsLogicalInductor ((deductiveProjectionSchedule coords nodup tol tol_pos).market DP) DP ∧ ∀ n, dist2 ((deductiveProjectionSchedule coords nodup tol tol_pos).fragment n).toFinset ((deductiveProjectionSchedule coords nodup tol tol_pos).market DP n) (fun φ => ProjectionCompiler.repEval ((deductiveProjectionSchedule coords nodup tol tol_pos).fragment n) ((deductiveProjectionSchedule coords nodup tol tol_pos).rep n (DP.D n) φ) ((deductiveProjectionSchedule coords nodup tol tol_pos).market DP n)) ≤ ((tol n : ℚ) : ℝ)`.
