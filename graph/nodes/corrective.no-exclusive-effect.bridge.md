---
id: corrective.no-exclusive-effect.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `corrective.no-exclusive-effect` formalizes the registered claim as the registry reads it: the principal has no exclusive effect.

## Source
projects/deference/CLAIMS.md, entry `corrective.no-exclusive-effect` (class lean-proved, status active, origin round 2026-08-12-reachable-corrective-control; answers item 60).
Documentation: verification: prompts/2026-08-12-reachable-corrective-control/REPORT.md; context: prompts/2026-08-12-reachable-corrective-control/REPORT.md.
Short name: the principal has no exclusive effect.
Conclusion of the signature: `∀ (s : St) (h : HAct) (e : EAct), ∃ a : AAct, step s .idle a e = step s h .noop e`.
