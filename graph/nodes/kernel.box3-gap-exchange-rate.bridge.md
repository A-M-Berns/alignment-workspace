---
id: kernel.box3-gap-exchange-rate.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `kernel.box3-gap-exchange-rate` formalizes the registered claim as the registry reads it (the short name is in the Source).

## Source
projects/deference/CLAIMS.md, entry `kernel.box3-gap-exchange-rate` (class lean-proved, status active, origin round 2026-09-27-corrigibility-kernel-phase2; answers item 104).
Documentation: verification: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md; context: prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md.
Short name: Box 3: compromise risk p for gain g against safe V₀ is accepted iff p(V₀ + g − c) ≤ g, hence only if p ≤ g/(g + |w_hi|).
Conclusion of the signature: `(V₀ ≤ (1 - p) * (V₀ + g) + p * c ↔ p * (V₀ + g - c) ≤ g) ∧ (p * (V₀ + g - c) ≤ g → p ≤ g / (g + |B.whi|))`.
