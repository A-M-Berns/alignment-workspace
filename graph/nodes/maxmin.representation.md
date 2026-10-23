---
id: maxmin.representation
kind: and
children: [maxmin.representation.record, maxmin.representation.bridge, maxmin.representation.complete, maxmin.representation.setting, maxmin.representation.h1, maxmin.representation.h2, maxmin.representation.h3, maxmin.representation.h4]
work: [{kind: round, ref: projects/normativity/rounds/2026-08-18-maxmin-representation}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
Ovchinnikov Theorem 4.1(a), for a nonempty convex domain in a topological real vector space. The source's proof silently needs full-dimensionality; the statement does not, and the round's errata carry a counterexample to the source's own nonemptiness claim.

## Source
projects/normativity/CLAIMS.md, entry `maxmin.representation` (class lean-proved, status active, origin round 2026-08-18-maxmin-representation; answers item 50).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-18-maxmin-representation/README.md.
The signature of `Workspace.Normativity.Contrib.MaxMinRepresentation.exists_maxMin_representation` in lean/Workspace/Normativity/Contrib/MaxMinRepresentation.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; the hypotheses are the signature's explicit proposition binders, tagged open unless the registry settles them, and the data binders are the setting leaf. Registry note: Ovchinnikov Theorem 4.1(a), for a nonempty convex domain in a topological real vector space. The source's proof silently needs full-dimensionality; the statement does not, and the round's errata carry a counterexample to the source's own nonemptiness claim.
