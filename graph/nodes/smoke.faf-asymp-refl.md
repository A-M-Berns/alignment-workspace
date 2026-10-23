---
id: smoke.faf-asymp-refl
kind: and
children: [smoke.faf-asymp-refl.record, smoke.faf-asymp-refl.bridge, smoke.faf-asymp-refl.complete, smoke.faf-asymp-refl.h1]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
work:
  - {kind: round, ref: prompts/2026-08-10-repo-scaffolding}
  - {kind: decision, ref: 2026-08-11--setup-scrub-reports-removed-root}
author: "@smithy-verity"
---
## Statement
Reaches a real declaration in the pinned dependency. Certifies the chain, not mathematics.

## Source
projects/normativity/CLAIMS.md, entry `smoke.faf-asymp-refl` (class lean-proved, status active, origin round 2026-08-10-repo-scaffolding; answers item 13).
Documentation: verification: prompts/2026-08-10-repo-scaffolding/REPORT.md; context: README.md.
The signature of `Workspace.Smoke.faf_asympEq_refl` in lean/Workspace/Smoke.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; the hypotheses are the signature's explicit proposition binders, tagged open unless the registry settles them, and the data binders are the setting leaf. Registry note: Reaches a real declaration in the pinned dependency. Certifies the chain, not mathematics.
