---
id: statistical.slack-floor-bounded.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.StatisticalConditions.DualCertifiedMarket.accountBounded_of_eventually_slack
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@claude-fable-5-2"
registry_id: statistical.slack-floor-bounded
---
## Statement
The declaration Workspace.Normativity.Contrib.StatisticalConditions.DualCertifiedMarket.accountBounded_of_eventually_slack is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `statistical.slack-floor-bounded` (class lean-proved, status active, origin round 2026-11-12-statistical-conditions; answers item 138).
Documentation: verification: projects/normativity/rounds/2026-11-12-statistical-conditions/THEOREM.md; context: projects/normativity/rounds/2026-11-12-statistical-conditions/REPORT.md.
The signature of `Workspace.Normativity.Contrib.StatisticalConditions.DualCertifiedMarket.accountBounded_of_eventually_slack` (theorem) in lean/Workspace/Normativity/Contrib/StatisticalConditions.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (φ : ℕ → Sentence) (c : ℚ) (hc0 : 0 ≤ c)
        (hC : M.C = floors φ (fun _ => c)) (δ : ℝ) (hδ : 0 < δ) (N₀ : ℕ)
        (hslack : ∀ n, N₀ ≤ n → (c : ℝ) + δ ≤ M.P n (φ n)) :
        M.AccountBounded ((c : ℝ) * (M.epsTotal / δ + ∑ n ∈ Finset.range N₀, M.mu n 0))
