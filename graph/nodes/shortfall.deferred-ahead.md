---
id: shortfall.deferred-ahead
kind: and
children: [shortfall.deferred-ahead.record, shortfall.deferred-ahead.bridge, shortfall.deferred-ahead.complete, shortfall.deferred-ahead.setting, shortfall.deferred-ahead.h1, shortfall.deferred-ahead.h2, shortfall.deferred-ahead.h3, shortfall.deferred-ahead.h4, shortfall.deferred-ahead.h5, shortfall.deferred-ahead.h6]
work: [{kind: round, ref: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
`shortfallProcess short defer` adjoins each option's decision at stage `defer j` (`shortDecision_mem`, `shortDecision_not_mem`); `lic_provind_true` over `DP.union (shortfallProcess …)`; `deferred_price_eventually_ge` is the price statement alone, `deferred_price_eventually_le` the dual for a non-shortfall. Inhabited: the table's world is consistent with every stage (`shortfallProcess_world`, `union_world`), so the consistency hypothesis holds for the pure process and over any base the world is consistent with; the inductor over the union is a hypothesis (the pinned criterion's).

## Source
projects/deference/CLAIMS.md, entry `shortfall.deferred-ahead` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/FOLLOWUP.md.
The signature of `Workspace.Deference.Contrib.ShortfallSecurity.deferred_ahead` in lean/Workspace/Deference/Contrib/ShortfallSecurity.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; the hypotheses are the signature's explicit proposition binders, tagged open unless the registry settles them, and the data binders are the setting leaf. Registry note: `shortfallProcess short defer` adjoins each option's decision at stage `defer j` (`shortDecision_mem`, `shortDecision_not_mem`); `lic_provind_true` over `DP.union (shortfallProcess …)`; `deferred_price_eventually_ge` is the price statement alone, `deferred_price_eventually_le` the dual for a non-shortfall. Inhabited: the table's world is consistent with every stage (`shortfallProcess_world`, `union_world`), so the consistency hypothesis holds for the pure process and over any base the world is consistent with; the inductor over the union is a hypothesis (the pinned criterion's). What it does not say: that the deferral or the process is computable — `DeductiveProcessComputation` is not built.
