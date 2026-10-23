---
id: corrective.can-correct-iff.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `corrective.can-correct-iff` formalizes the registered claim as the registry reads it: corrective capability characterised at the field level.

## Source
projects/deference/CLAIMS.md, entry `corrective.can-correct-iff` (class lean-proved, status active, origin round 2026-08-12-reachable-corrective-control; answers item 60).
Documentation: verification: prompts/2026-08-12-reachable-corrective-control/REPORT.md; context: prompts/2026-08-12-reachable-corrective-control/REPORT.md.
Short name: corrective capability characterised at the field level.
Conclusion of the signature: `∀ s : St, CanCorrect s ↔ (s.channel = .intact ∧ s.world = .two)`.
