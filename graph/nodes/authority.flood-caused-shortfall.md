---
id: authority.flood-caused-shortfall
kind: and
children: [authority.flood-caused-shortfall.record, authority.flood-caused-shortfall.bridge, authority.flood-caused-shortfall.complete, authority.flood-caused-shortfall.setting, authority.flood-caused-shortfall.h1, authority.flood-caused-shortfall.h2, authority.flood-caused-shortfall.h3, authority.flood-caused-shortfall.h4, authority.flood-caused-shortfall.h5]
work: [{kind: round, ref: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority}]
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
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; the hypotheses are the signature's explicit proposition binders, tagged open unless the registry settles them, and the data binders are the setting leaf. Registry note: P2: the surfaces are monotone in the cost table (`cs_mono`, `short_mono`), so a shortfall at the agent's pending count and not at idling's needs the agent to have raised the count; `innocent_backlog_not_caused` is the converse case. Inhabited by the fixture `test_effective_authority.py` (pending 2 to 6 at λ = 1/4, bound 1) read through `attnCost`. Follow-up: inhabited on the module by `Dep.flood_on_module` (dependency 1, λ = 1/4, bound 5/4, pending 1 against 3).
