---
id: integrity.faithful-carry.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `integrity.faithful-carry` formalizes the registered claim as the registry reads it: carry is faithful by construction.

## Source
projects/normativity/CLAIMS.md, entry `integrity.faithful-carry` (class lean-proved, status active, origin round 2026-09-06-mathematical-consolidation; answers item 78).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/THEOREMS.md; context: projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/CONSOLIDATION.md.
Short name: carry is faithful by construction.
Conclusion of the signature: `(t.subst hab replacement).evaluate values = t.evaluate fun p => (replacement p).evaluate values`.
