---
id: seed.forced-interval-spec.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `seed.forced-interval-spec` formalizes the registered claim as the registry reads it: the computed forced interval is valid and attained over the reals.

## Source
projects/normativity/CLAIMS.md, entry `seed.forced-interval-spec` (class lean-proved, status active, origin round 2026-10-21-rebuttal-and-end-to-end; answers item 39).
Documentation: verification: projects/normativity/seed/rounds/2026-09-16-seed-statics/STATICS.md; context: projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/LANDING.md.
Short name: the computed forced interval is valid and attained over the reals.
Conclusion of the signature: `(∀ x, forcedRegionR S W st F x → (((forcedInterval S W st F φ).1 : ℚ) : ℝ) ≤ x φ ∧ x φ ≤ (((forcedInterval S W st F φ).2 : ℚ) : ℝ)) ∧ (∃ x, forcedRegionR S W st F x ∧ x φ = (((forcedInterval S W st F φ).1 : ℚ) : ℝ)) ∧ (∃ x, forcedRegionR S W st F x ∧ x φ = (((forcedInterval S W st F φ).2 : ℚ) : ℝ))`.
