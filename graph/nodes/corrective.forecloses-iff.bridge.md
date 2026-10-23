---
id: corrective.forecloses-iff.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `corrective.forecloses-iff` formalizes the registered claim as the registry reads it: foreclosure characterised at the field level.

## Source
projects/deference/CLAIMS.md, entry `corrective.forecloses-iff` (class lean-proved, status active, origin round 2026-08-12-reachable-corrective-control; answers item 60).
Documentation: verification: prompts/2026-08-12-reachable-corrective-control/REPORT.md; context: prompts/2026-08-12-reachable-corrective-control/REPORT.md.
Short name: foreclosure characterised at the field level.
Conclusion of the signature: `Forecloses s a ↔ (s.channel = .intact ∧ ∀ (h : HAct) (e : EAct), (step s h a e).channel = .severed)`.
