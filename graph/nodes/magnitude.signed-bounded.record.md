---
id: magnitude.signed-bounded.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.MagnitudePrediction.signed_bddAbove_of_bddBelow
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: magnitude.signed-bounded
---
## Statement
The declaration Workspace.Deference.Contrib.MagnitudePrediction.signed_bddAbove_of_bddBelow is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `magnitude.signed-bounded` (class lean-proved, status active, origin round 2026-08-11-phase-ii-prediction; answers item 21).
Documentation: verification: prompts/2026-08-11-phase-ii-prediction/REPORT.md; context: prompts/2026-08-11-phase-ii-prediction/REPORT.md.
The signature of `Workspace.Deference.Contrib.MagnitudePrediction.signed_bddAbove_of_bddBelow` (theorem) in lean/Workspace/Deference/Contrib/MagnitudePrediction.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (φ : ℕ → Sentence) (P : History) (DP : DeductiveProcess)
        [hLI : IsLogicalInductor P DP] (hEC : EfficientlyComputable (unitTrader φ))
        (hbelow : BddBelow ((unitTrader φ).plausibleAssessments P DP)) :
        BddAbove ((unitTrader φ).plausibleAssessments P DP)
