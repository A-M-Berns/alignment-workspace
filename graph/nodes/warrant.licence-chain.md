---
id: warrant.licence-chain
kind: and
children: [warrant.licence-chain.record, warrant.licence-chain.bridge, warrant.licence-chain.complete, warrant.licence-chain.h-record-state, warrant.licence-chain.h-verdict-certificate, warrant.licence-chain.h-supported, warrant.licence-chain.h-authorized-event]
work: [{kind: round, ref: projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics}, {kind: priorities, ref: 56}, {kind: round, ref: projects/enabling/rounds/2026-10-24-site-vertical-slice}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
A licensed verdict is supported on the record's grounds and admissible in their region; supported-to-admissible is by rational convexity of the bundle's region (region_convex), not a projection.

## Source
projects/normativity/CLAIMS.md, entry `warrant.licence-chain` (class lean-proved, status active, origin round 2026-10-20-warrant-enforcement-semantics; answers item 56).
Documentation: verification: projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/LICENCE_CHAIN.md; context: projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/COUNTERMODELS.md.
The signature of `Workspace.Normativity.Contrib.WarrantEntitlement.licence_chain` in lean/Workspace/Normativity/Contrib/WarrantEntitlement.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature. The site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice) connected it by reading: its hypotheses are the four leaves, one of which restates the conclusion's first conjunct (Licensed → Supported is the definition of Licensed), its bridge names the gap between the claim and the declaration, and it is a conjunct of the informal claim verdict-licence-chain, a shared-claim root of normative-inductor, rather than a node that frame holds. Registry note: A licensed verdict is supported on the record's grounds and admissible in their region; supported-to-admissible is by rational convexity of the bundle's region (region_convex), not a projection. The registry's `answers_item` is the `priorities` pointer to item 56 (ruling F2).
