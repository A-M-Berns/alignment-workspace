---
id: legitimacy.endpoint-only-insufficient
kind: and
children: [legitimacy.endpoint-only-insufficient.record, legitimacy.endpoint-only-insufficient.bridge, legitimacy.endpoint-only-insufficient.complete]
superseded_by: openness.endpoint-only-insufficient
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
work:
  - {kind: round, ref: projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass}
  - {kind: decision, ref: 2026-09-25--legitimacy-internal-external-robust-openness-external}
author: "@smithy-verity"
---
## Statement
Exact counterexample: a two-transition evolution open at both endpoints whose middle state has a live concern with no adequate route; it is not a legitimate segment. This is why openness is required at every state.

## Source
projects/normativity/CLAIMS.md, entry `legitimacy.endpoint-only-insufficient` (class lean-proved, status superseded, origin round 2026-09-07-final-pressure-pass; answers item 78).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/THEOREMS.md; context: projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/READINESS.md.
The signature of `Workspace.Normativity.Contrib.LegitimateEvolution.Witness.endpoint_only_insufficient` in lean/Workspace/Normativity/Contrib/OpenIntegrityEvolution.lean (an alias declared in lean/Workspace/Normativity/Contrib/LegitimateEvolution.lean).

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; the hypotheses are the signature's explicit proposition binders, tagged open unless the registry settles them, and the data binders are the setting leaf. Registry note: Exact counterexample: a two-transition evolution open at both endpoints whose middle state has a live concern with no adequate route; it is not a legitimate segment. This is why openness is required at every state. Superseded 2026-09-25 by `openness.endpoint-only-insufficient`; the declaration name is kept resolving by a deprecated alias for one release.
