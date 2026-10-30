---
id: authority.revocation-default
kind: and
children: [authority.revocation-default.record, authority.revocation-default.bridge, authority.revocation-default.complete, authority.revocation-default.h-fixture]
work: [{kind: round, ref: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority}, {kind: priorities, ref: 107}, {kind: round, ref: projects/enabling/rounds/2026-10-24-site-vertical-slice}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
Re-pointed by the follow-up (prompts/2026-10-01-thin-legitimacy-and-effective-authority/FOLLOWUP.md, Part 4) from `atrophy_counted_by_default`, arithmetic on four numbers that did not use the module. `Dep.revocationJ` is the entry of `AuthAlloc`; `Dep.depI` the interaction whose correction *revoke at level d* costs d; `revocation_short_iff`, `build_caused_iff`, `build_entrenches` (the crossing is the landed `EntrenchAt`).

## Source
projects/deference/CLAIMS.md, entry `authority.revocation-default` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.EffectiveAuthority.Dep.atrophy_on_module` in lean/Workspace/Deference/Contrib/EffectiveAuthority.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature. The site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice) connected it by reading: its hypotheses are filed as leaves, its bridge names the gap between the claim and the declaration, and it is one of the twelve conjuncts of the informal claim effective-authority-layer (the effective-authority layer), a shared-claim root of authorship-and-transparency and public-corrigibility-line, rather than a node a frame holds. The registry's `answers_item` is the `priorities` pointer to item 107 (ruling F2).
