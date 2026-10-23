---
id: region.hull
kind: and
children: [region.hull.record, region.hull.bridge, region.hull.complete, region.hull.setting, region.hull.h1]
work: [{kind: round, ref: projects/normativity/rounds/2026-08-19-deductive-region}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
An image equality, which is the form with content: membership is defined through the hull, so the unfolding form is definitional and says nothing. Duplicate-freeness of the fragment is used in the surjectivity direction only.

## Source
projects/normativity/CLAIMS.md, entry `region.hull` (class lean-proved, status active, origin round 2026-08-19-deductive-region; answers item 51).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: prompts/2026-08-19-deductive-region/REPORT.md.
The signature of `Workspace.Normativity.Contrib.DeductiveRegion.deductiveRegion_eq_convexHull` in lean/Workspace/Normativity/Contrib/DeductiveRegion.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; the hypotheses are the signature's explicit proposition binders, tagged open unless the registry settles them, and the data binders are the setting leaf. Registry note: An image equality, which is the form with content: membership is defined through the hull, so the unfolding form is definitional and says nothing. Duplicate-freeness of the fragment is used in the surjectivity direction only. The predicate is not a decision procedure: membership of an arbitrary real price vector is not decided here.
