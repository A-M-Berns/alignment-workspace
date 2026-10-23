---
id: maxmin.representation.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `maxmin.representation` formalizes the registered claim as the registry reads it: a piecewise affine function is a max of mins of its components.

## Source
projects/normativity/CLAIMS.md, entry `maxmin.representation` (class lean-proved, status active, origin round 2026-08-18-maxmin-representation; answers item 50).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-18-maxmin-representation/README.md.
Short name: a piecewise affine function is a max of mins of its components.
Conclusion of the signature: `∃ (m : ℕ) (S : Fin (m + 1) → Finset ι) (hS : ∀ j, (S j).Nonempty), ∀ x ∈ Γ, f x = Finset.univ.sup' Finset.univ_nonempty fun j => (S j).inf' (hS j) fun i => g i x`.
