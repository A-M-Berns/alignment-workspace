---
id: deconfusing.corollary-b.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `deconfusing.corollary-b` formalizes the registered claim as the registry reads it: Corollary (Exploration) (b): for any available a'_k, limsup_K ((1/K) Σ_{k<K} (U_k a'_k − S_k) − ε_K λ (τ + θ)) ≤ 0.

## Source
projects/deference/CLAIMS.md, entry `deconfusing.corollary-b` (class lean-proved, status active, origin round 2026-10-17-post-companion-formalization; answers item 107).
Documentation: verification: prompts/2026-10-17-post-companion-formalization/REPORT.md; context: prompts/2026-10-17-post-companion-formalization/PROMPT.md; companion: wiki/Deconfusing-Corrigibility-Companion.md.
Short name: Corollary (Exploration) (b): for any available a'_k, limsup_K ((1/K) Σ_{k<K} (U_k a'_k − S_k) − ε_K λ (τ + θ)) ≤ 0.
Conclusion of the signature: `LimsupLE (fun K => X.excess a' K - X.ε K * (X.lam * (X.τ + X.θ))) 0`.
