---
id: integrity.receipts-immutable
kind: and
children: [integrity.receipts-immutable.record, integrity.receipts-immutable.bridge, integrity.receipts-immutable.complete, integrity.receipts-immutable.setting, integrity.receipts-immutable.h1, integrity.receipts-immutable.h2]
work: [{kind: round, ref: projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
Substitution at live ports keeps every terminal receipt and adds only the terminals of the substituted accounts. With `livePorts_subst` this is the three-fate accounting at the leaf level: terminal fates persist, live leaves are replaced.

## Source
projects/normativity/CLAIMS.md, entry `integrity.receipts-immutable` (class lean-proved, status active, origin round 2026-09-06-mathematical-consolidation; answers item 78).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/THEOREMS.md; context: projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/CONSOLIDATION.md.
The signature of `Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.terminals_subst` in lean/Workspace/Normativity/Contrib/OccurrenceIntegrity.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; the hypotheses are the signature's explicit proposition binders, tagged open unless the registry settles them, and the data binders are the setting leaf. Registry note: Substitution at live ports keeps every terminal receipt and adds only the terminals of the substituted accounts. With `livePorts_subst` this is the three-fate accounting at the leaf level: terminal fates persist, live leaves are replaced. Renamed 2026-09-25 (the legitimacy-internal-external round): an Integrity result stated in `OccurrenceIntegrity`; the id names the component.
