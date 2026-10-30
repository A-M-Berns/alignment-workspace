---
id: compiler.constraints-end-to-end.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `compiler.constraints-end-to-end` formalizes the registered claim as the registry reads it: the constraint schedule's effective market is a logical inductor.

## Source
projects/normativity/CLAIMS.md, entry `compiler.constraints-end-to-end` (class lean-proved, status active, origin round 2026-08-18-projection-enforcement; answers item 48).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-18-projection-enforcement/FINAL_FORMALIZATION_STATUS.md.
Short name: the constraint schedule's effective market is a logical inductor.
Conclusion of the signature: `IsLogicalInductor (C.market (effectiveRepresentation C) DP) DP ∧ (∀ n, dist2 (C.fragment n).toFinset (C.market (effectiveRepresentation C) DP n) (C.target (effectiveRepresentation C) DP n) ≤ ((C.tol n : ℚ) : ℝ)) ∧ ∀ n, C.regionPred n (C.target (effectiveRepresentation C) DP n) ∧ ∀ φ ∈ (C.fragment n).toFinset, |C.market (effectiveRepresentation C) DP n φ - C.target (effectiveRepresentation C) DP n φ| ≤ ((C.tol n : ℚ) : ℝ)`.
