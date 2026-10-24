---
id: compiler.schedule-end-to-end.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `compiler.schedule-end-to-end` formalizes the registered claim as the registry reads it: the projection schedule's effective market is a logical inductor.

## Source
projects/normativity/CLAIMS.md, entry `compiler.schedule-end-to-end` (class lean-proved, status active, origin round 2026-08-18-projection-enforcement; answers item 48).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-18-projection-enforcement/FINAL_FORMALIZATION_STATUS.md.
Short name: the projection schedule's effective market is a logical inductor.
Conclusion of the signature: `IsLogicalInductor (S.market DP) DP ∧ (∀ n, dist2 (S.fragment n).toFinset (S.market DP n) (q n) ≤ ((S.tol n : ℚ) : ℝ)) ∧ ∀ n, K n (q n) ∧ ∀ φ ∈ (S.fragment n).toFinset, |S.market DP n φ - q n φ| ≤ ((S.tol n : ℚ) : ℝ)`.
