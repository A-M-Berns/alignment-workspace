---
id: force.strategy-value.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `force.strategy-value` formalizes the registered claim as the registry reads it: the enforcement position's exact rational market value.

## Source
projects/normativity/CLAIMS.md, entry `force.strategy-value` (class lean-proved, status active, origin round 2026-08-16-traderized-enforcement; answers item 41).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-16-traderized-enforcement/ENFORCEMENT.md.
Short name: the enforcement position's exact rational market value.
Conclusion of the signature: `(enforcementStrategy pres n).marketValueRat Q w = pair pres.coords (pres.compiledPosition (Q n)) (fun φ => w φ - Q n φ)`.
