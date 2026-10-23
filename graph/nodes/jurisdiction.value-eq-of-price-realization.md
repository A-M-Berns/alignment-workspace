---
id: jurisdiction.value-eq-of-price-realization
kind: and
children: [jurisdiction.value-eq-of-price-realization.record, jurisdiction.value-eq-of-price-realization.bridge, jurisdiction.value-eq-of-price-realization.complete]
work: [{kind: round, ref: prompts/2026-08-11-stage-v-li-native}, {kind: priorities, ref: 28}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
The polymorphic factorization: a valuation whose only inputs are realization maps priced by one measure cannot see anything else.

## Source
projects/deference/CLAIMS.md, entry `jurisdiction.value-eq-of-price-realization` (class lean-proved, status active, origin round 2026-08-11-stage-v-li-native; answers item 28).
Documentation: verification: prompts/2026-08-11-stage-v-li-native/REPORT.md; context: prompts/2026-08-11-stage-v-li-native/REPORT.md.
The signature of `Workspace.Deference.Contrib.StaticViewFactorization.value_eq_of_price_realization_eq` in lean/Workspace/Deference/Contrib/StaticViewFactorization.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. Registry note: The polymorphic factorization: a valuation whose only inputs are realization maps priced by one measure cannot see anything else. The registry's `answers_item` is the `priorities` pointer to item 28 (ruling F2).
