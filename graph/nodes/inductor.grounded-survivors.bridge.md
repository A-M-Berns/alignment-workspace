---
id: inductor.grounded-survivors.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `inductor.grounded-survivors` formalizes the registered claim as the registry reads it: the survivors are the grounded fixed point.

## Source
projects/normativity/CLAIMS.md, entry `inductor.grounded-survivors` (class lean-proved, status active, origin round 2026-10-22-normative-inductor-integration; answers item 112).
Documentation: verification: projects/normativity/rounds/2026-10-22-normative-inductor-integration/THEOREM_STORY.md; context: projects/normativity/rounds/2026-10-22-normative-inductor-integration/HANDOFFS.md.
Short name: the survivors are the grounded fixed point.
Conclusion of the signature: `o ∈ G.survivors st F ↔ o ∈ G ∧ ¬ undercut st o ∧ settleOutcome F o.form = .kept ∧ ∀ j, o.cites = .occurrence j → ∃ o' ∈ G.survivors st F, o'.id = j`.
