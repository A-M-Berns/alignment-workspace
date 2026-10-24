---
id: magnitude.signed-bounded-actual.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.MagnitudePrediction.signed_bddAbove_of_bddBelow_rpn
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: magnitude.signed-bounded-actual
---
## Statement
The declaration Workspace.Deference.Contrib.MagnitudePrediction.signed_bddAbove_of_bddBelow_rpn is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `magnitude.signed-bounded-actual` (class lean-proved, status active, origin round 2026-08-11-stage-v-li-native; answers item 21).
Documentation: verification: prompts/2026-08-11-stage-v-li-native/REPORT.md; context: prompts/2026-08-11-stage-v-li-native/REPORT.md.
The signature of `Workspace.Deference.Contrib.MagnitudePrediction.signed_bddAbove_of_bddBelow_rpn` (theorem) in lean/Workspace/Deference/Contrib/MagnitudePrediction.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (φ : ℕ → Sentence) (P : History)
        (DP : DeductiveProcess) [IsLogicalInductor P DP] (hφ : RpnSentenceCodes φ)
        (hbelow : BddBelow ((unitTrader φ).plausibleAssessments P DP)) :
        BddAbove ((unitTrader φ).plausibleAssessments P DP)
