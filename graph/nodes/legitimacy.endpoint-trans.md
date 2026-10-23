---
id: legitimacy.endpoint-trans
kind: and
children: [legitimacy.endpoint-trans.record, legitimacy.endpoint-trans.bridge, legitimacy.endpoint-trans.complete, legitimacy.endpoint-trans.setting, legitimacy.endpoint-trans.h1, legitimacy.endpoint-trans.h2]
superseded_by: open-integrity.endpoint-trans
work: [{kind: round, ref: projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
`Legitimate` is `Nonempty LegitimateSegment`; it hides the witness for consumers and is transitive. The certificate remains available for audit.

## Source
projects/normativity/CLAIMS.md, entry `legitimacy.endpoint-trans` (class lean-proved, status superseded, origin round 2026-09-07-final-pressure-pass; answers item 78).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/THEOREMS.md; context: projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/READINESS.md.
The signature of `Workspace.Normativity.Contrib.LegitimateEvolution.Legitimate.trans` in lean/Workspace/Normativity/Contrib/OpenIntegrityEvolution.lean (an alias declared in lean/Workspace/Normativity/Contrib/LegitimateEvolution.lean).

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; the hypotheses are the signature's explicit proposition binders, tagged open unless the registry settles them, and the data binders are the setting leaf. Registry note: `Legitimate` is `Nonempty LegitimateSegment`; it hides the witness for consumers and is transitive. The certificate remains available for audit. Superseded 2026-09-25 by `open-integrity.endpoint-trans`; the declaration name is kept resolving by a deprecated alias for one release.
