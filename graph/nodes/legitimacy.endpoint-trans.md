---
id: legitimacy.endpoint-trans
kind: and
children: [legitimacy.endpoint-trans.record, legitimacy.endpoint-trans.bridge, legitimacy.endpoint-trans.complete]
superseded_by: open-integrity.endpoint-trans
work: [{kind: round, ref: projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass}, {kind: priorities, ref: 78}]
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
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. Registry note: `Legitimate` is `Nonempty LegitimateSegment`; it hides the witness for consumers and is transitive. The certificate remains available for audit. Superseded 2026-09-25 by `open-integrity.endpoint-trans`; the declaration name is kept resolving by a deprecated alias for one release. The registry's `answers_item` is the `priorities` pointer to item 78 (ruling F2).
