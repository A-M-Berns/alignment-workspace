---
id: kernel.extension-realized-rate.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `kernel.extension-realized-rate` formalizes the registered claim as the registry reads it: The extension's interface theorem: avg π ≤ avg (D − c_k)/ϖ + ε̄ ((D − w)/ϖ + θ_hi) + (B(K) + M(K))/(ϖ Σ w_k).

## Source
projects/deference/CLAIMS.md, entry `kernel.extension-realized-rate` (class lean-proved, status active, origin round 2026-09-27-corrigibility-kernel-phase2; answers item 104).
Documentation: verification: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md; context: prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md.
Short name: The extension's interface theorem: avg π ≤ avg (D − c_k)/ϖ + ε̄ ((D − w)/ϖ + θ_hi) + (B(K) + M(K))/(ϖ Σ w_k).
Conclusion of the signature: `(∑ k ∈ range K, 𝓘.w k * 𝓘.π k) / (∑ k ∈ range K, 𝓘.w k) ≤ (∑ k ∈ range K, 𝓘.w k * (𝓘.D - 𝓘.c k)) / (𝓘.ϖ * ∑ k ∈ range K, 𝓘.w k) + (𝓘.explMass K / ∑ k ∈ range K, 𝓘.w k) * ((𝓘.D - 𝓘.lo) / 𝓘.ϖ + 𝓘.θhi) + (𝓘.B K + 𝓘.M K) / (𝓘.ϖ * ∑ k ∈ range K, 𝓘.w k)`.
