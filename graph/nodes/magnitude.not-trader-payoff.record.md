---
id: magnitude.not-trader-payoff.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.MagnitudePrediction.magnitude_not_traderPayoff
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: magnitude.not-trader-payoff
---
## Statement
The declaration Workspace.Deference.Contrib.MagnitudePrediction.magnitude_not_traderPayoff is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `magnitude.not-trader-payoff` (class lean-proved, status active, origin round 2026-08-11-phase-ii-prediction; answers item 21).
Documentation: verification: prompts/2026-08-11-phase-ii-prediction/REPORT.md; context: prompts/2026-08-11-phase-ii-prediction/REPORT.md.
The signature of `Workspace.Deference.Contrib.MagnitudePrediction.magnitude_not_traderPayoff` (theorem) in lean/Workspace/Deference/Contrib/MagnitudePrediction.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {P : History} (M : CoherentMixture P) (φ : ℕ → Sentence)
        (c : ℝ) (hc : 0 < c)
        (hrate : ∀ (j : Fin M.card) (n : ℕ), c * ((n : ℝ) + 1) ≤ magnitudeSum P φ (M.world j) n)
        (Tr : Trader) (K : ℝ) :
        ¬ (∀ (j : Fin M.card) (n : ℕ),
            magnitudeSum P φ (M.world j) n ≤ Tr.netWorth P (M.world j) n + K)
