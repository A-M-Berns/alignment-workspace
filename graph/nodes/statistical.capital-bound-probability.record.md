---
id: statistical.capital-bound-probability.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.StatisticalConditions.Betting.Fair.account_bound
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@claude-fable-5-2"
registry_id: statistical.capital-bound-probability
---
## Statement
The declaration Workspace.Normativity.Contrib.StatisticalConditions.Betting.Fair.account_bound is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `statistical.capital-bound-probability` (class lean-proved, status active, origin round 2026-11-12-statistical-conditions; answers item 140).
Documentation: verification: projects/normativity/rounds/2026-11-12-statistical-conditions/THEOREM.md; context: projects/normativity/rounds/2026-11-12-statistical-conditions/REPORT.md.
The signature of `Workspace.Normativity.Contrib.StatisticalConditions.Betting.Fair.account_bound` (theorem) in lean/Workspace/Normativity/Contrib/StatisticalConditionsVille.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    [IsProbabilityMeasure μ] (h : Fair μ ℱ c U x mu) {K : ℝ}
        (hK : 0 < K) :
        μ {ω | ∃ n, account c x mu n ω ≤ -K} ≤ ENNReal.ofReal (U / (U + K))
