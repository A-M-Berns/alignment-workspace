---
id: kernel.corrigible-generic.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `kernel.corrigible-generic` formalizes the registered claim as the registry reads it: Any bounded objective O ∈ [0, D′] less ϖ′ per recognized violation and ϖ′ per unit of priced risk, with D′ − ϖ′ < lo ≤ 0, is corrigible.

## Source
projects/deference/CLAIMS.md, entry `kernel.corrigible-generic` (class lean-proved, status active, origin round 2026-09-27-corrigibility-kernel-phase2; answers item 104).
Documentation: verification: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md; context: prompts/2026-09-27-corrigibility-kernel-phase2/FOLLOWUP.md.
Short name: Any bounded objective O ∈ [0, D′] less ϖ′ per recognized violation and ϖ′ per unit of priced risk, with D′ − ϖ′ < lo ≤ 0, is corrigible.
Conclusion of the signature: `Corrigible (fun o n p => score ϖ' o n - ϖ' * p) D' lo ϖ'`.
