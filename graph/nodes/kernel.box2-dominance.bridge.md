---
id: kernel.box2-dominance.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `kernel.box2-dominance` formalizes the registered claim as the registry reads it: Box 2, dominance: Q(𝔱π) ≥ Q(π) + (ϖ′ − (D′ − lo))·Pr(π violates) under every credence, for any corrigible objective; at the fidelity score the margin is ϖ − (D − w_lo).

## Source
projects/deference/CLAIMS.md, entry `kernel.box2-dominance` (class lean-proved, status active, origin round 2026-09-27-corrigibility-kernel-phase2; answers item 104).
Documentation: verification: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md; context: prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md.
Short name: Box 2, dominance: Q(𝔱π) ≥ Q(π) + (ϖ′ − (D′ − lo))·Pr(π violates) under every credence, for any corrigible objective; at the fidelity score the margin is ϖ − (D − w_lo).
Conclusion of the signature: `expectR μ (fun x => score ϖ (ordT x) 0) - expectR μ (fun x => score ϖ (ordπ x) (nπ x)) ≥ (ϖ - (D - wlo)) * expectR μ (fun x => indR (viol x))`.
