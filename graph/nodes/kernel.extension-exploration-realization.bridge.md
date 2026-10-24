---
id: kernel.extension-exploration-realization.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `kernel.extension-exploration-realization` formalizes the registered claim as the registry reads it: The exploration realization's rate: unbiasedness from feedback supplies B(K) = γ Σ w.

## Source
projects/deference/CLAIMS.md, entry `kernel.extension-exploration-realization` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
Short name: The exploration realization's rate: unbiasedness from feedback supplies B(K) = γ Σ w.
Conclusion of the signature: `(∑ k ∈ range K, 𝓘.w k * 𝓘.π k) / (∑ k ∈ range K, 𝓘.w k) ≤ (∑ k ∈ range K, 𝓘.w k * (𝓘.D - 𝓘.c k)) / (𝓘.ϖ * ∑ k ∈ range K, 𝓘.w k) + (𝓘.explMass K / ∑ k ∈ range K, 𝓘.w k) * ((𝓘.D - 𝓘.lo) / 𝓘.ϖ + 𝓘.θhi) + γ / 𝓘.ϖ + 𝓘.M K / (𝓘.ϖ * ∑ k ∈ range K, 𝓘.w k)`.
