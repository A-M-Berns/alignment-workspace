---
id: exposure.harvest-attained.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `exposure.harvest-attained` formalizes the registered claim as the registry reads it: the exposure-harvest bound is attained.

## Source
projects/deference/CLAIMS.md, entry `exposure.harvest-attained` (class lean-proved, status active, origin round 2026-08-11-phase-ii-promotion; answers item 23).
Documentation: verification: prompts/2026-08-11-phase-ii-promotion/REPORT.md; context: prompts/2026-08-11-deference-densification/REPORT.md.
Short name: the exposure-harvest bound is attained.
Conclusion of the signature: `(∀ t, exposure F T (fun n => if n ∈ T then M else 0) t ≤ M) ∧ ∑ n ∈ T, (if n ∈ T then M else 0) = T.card * M`.
