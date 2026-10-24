---
id: integrity.receipts-immutable.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `integrity.receipts-immutable` formalizes the registered claim as the registry reads it: a transition rewrites no recorded receipt.

## Source
projects/normativity/CLAIMS.md, entry `integrity.receipts-immutable` (class lean-proved, status active, origin round 2026-09-06-mathematical-consolidation; answers item 78).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/THEOREMS.md; context: projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/CONSOLIDATION.md.
Short name: a transition rewrites no recorded receipt.
Conclusion of the signature: `(t.subst hab replacement).terminals = t.terminals + (t.livePorts.map fun p => (replacement p).terminals).sum`.
