---
id: maxmin.converse.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `maxmin.converse` formalizes the registered claim as the registry reads it: a max of mins of affine components is piecewise affine.

## Source
projects/normativity/CLAIMS.md, entry `maxmin.converse` (class lean-proved, status active, origin round 2026-08-18-maxmin-representation; answers item 50).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-18-maxmin-representation/README.md.
Short name: a max of mins of affine components is piecewise affine.
Conclusion of the signature: `IsPiecewiseAffineOn Γ (fun x => Finset.univ.sup' Finset.univ_nonempty fun j => (S j).inf' (hS j) fun i => g i x) g`.
