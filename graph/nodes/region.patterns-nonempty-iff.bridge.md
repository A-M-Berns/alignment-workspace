---
id: region.patterns-nonempty-iff.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `region.patterns-nonempty-iff` formalizes the registered claim as the registry reads it: the enumeration is nonempty exactly when the stage is satisfiable.

## Source
projects/normativity/CLAIMS.md, entry `region.patterns-nonempty-iff` (class lean-proved, status active, origin round 2026-08-19-deductive-region; answers item 51).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: prompts/2026-08-19-deductive-region/REPORT.md.
Short name: the enumeration is nonempty exactly when the stage is satisfiable.
Conclusion of the signature: `admissiblePatterns D coords ≠ [] ↔ ∃ v : PCWorld, v.ConsistentWith D`.
