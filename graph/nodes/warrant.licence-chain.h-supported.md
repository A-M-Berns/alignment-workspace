---
id: warrant.licence-chain.h-supported
kind: leaf
leaf_kind: hypothesis
discharge: restates-conclusion
author: "@smithy-verity"
size: S
size_reason: "one hypothesis of the declaration, read"
version: 1
---
## Statement
The certificate's positively weighted rows are cited into the settled bundle, its endpoints bracket the verdict, and both endpoints are attained in the bundle's region (the verdict is Supported).

## Source
projects/normativity/CLAIMS.md, entry `warrant.licence-chain` (class lean-proved, status active, origin round 2026-10-20-warrant-enforcement-semantics; answers item 56).
The signature of `Workspace.Normativity.Contrib.WarrantEntitlement.licence_chain` and the definitions `Admissible`, `SupportedOn`, `Supported`, `RecordState` and `Licensed` in lean/Workspace/Normativity/Contrib/WarrantEntitlement.lean; projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/LICENCE_CHAIN.md, A2 (the chain); read by the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice).

## Notes
The first conjunct of `h : Licensed R φ v c event`, since Licensed is defined as Supported together with an authorized event. It restates the conclusion's first conjunct verbatim: the arrow Licensed → Supported is the definition of Licensed read back, and only the arrow Supported → Admissible has content (rational convexity of the settled region, `region_convex`). This is the finding the level rule exists for: the result's first half is a restatement, its second half a one-line theorem on a definition.
