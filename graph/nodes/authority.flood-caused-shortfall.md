---
id: authority.flood-caused-shortfall
kind: and
children: [authority.flood-caused-shortfall.record, authority.flood-caused-shortfall.bridge, authority.flood-caused-shortfall.complete, authority.flood-caused-shortfall.h-flood-shortfall]
work: [{kind: round, ref: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority}, {kind: priorities, ref: 107}, {kind: round, ref: projects/enabling/rounds/2026-10-24-site-vertical-slice}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
P2: the surfaces are monotone in the cost table (`cs_mono`, `short_mono`), so a shortfall at the agent's pending count and not at idling's needs the agent to have raised the count; `innocent_backlog_not_caused` is the converse case. Inhabited by the fixture `test_effective_authority.py` (pending 2 to 6 at λ = 1/4, bound 1) read through `attnCost`.

## Source
projects/deference/CLAIMS.md, entry `authority.flood-caused-shortfall` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.EffectiveAuthority.flood_raises_pending` in lean/Workspace/Deference/Contrib/EffectiveAuthority.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature. The site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice) connected it by reading: its hypotheses are filed as leaves, its bridge names the gap between the claim and the declaration, and it is one of the twelve conjuncts of the informal claim effective-authority-layer (the effective-authority layer), a shared-claim root of authorship-and-transparency and public-corrigibility-line, rather than a node a frame holds. The registry's `answers_item` is the `priorities` pointer to item 107 (ruling F2).
