---
id: jurisdiction.value-eq-of-price-realization.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.StaticViewFactorization.value_eq_of_price_realization_eq
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: jurisdiction.value-eq-of-price-realization
---
## Statement
The declaration Workspace.Deference.Contrib.StaticViewFactorization.value_eq_of_price_realization_eq is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `jurisdiction.value-eq-of-price-realization` (class lean-proved, status active, origin round 2026-08-11-stage-v-li-native; answers item 28).
Documentation: verification: prompts/2026-08-11-stage-v-li-native/REPORT.md; context: prompts/2026-08-11-stage-v-li-native/REPORT.md.
The signature of `Workspace.Deference.Contrib.StaticViewFactorization.value_eq_of_price_realization_eq` (theorem) in lean/Workspace/Deference/Contrib/StaticViewFactorization.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {Architecture : Type uA} {Price : Type uP} {Realization : Type uR} {Value : Type uV}
        {price : Architecture → Price} {realization : Architecture → Realization}
        {value : Architecture → Value} {left right : Architecture}
        (hfactor : FactorsThroughStaticView price realization value)
        (hprice : price left = price right)
        (hrealization : realization left = realization right) :
        value left = value right
