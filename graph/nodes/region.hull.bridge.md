---
id: region.hull.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `region.hull` formalizes the registered claim as the registry reads it: the region restricted to the fragment is the hull of the vertex list.

## Source
projects/normativity/CLAIMS.md, entry `region.hull` (class lean-proved, status active, origin round 2026-08-19-deductive-region; answers item 51).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: prompts/2026-08-19-deductive-region/REPORT.md.
Short name: the region restricted to the fragment is the hull of the vertex list.
Conclusion of the signature: `restrictTo coords '' {p | deductiveRegion D coords p} = convexHull ℝ (deductiveVertices D coords)`.
