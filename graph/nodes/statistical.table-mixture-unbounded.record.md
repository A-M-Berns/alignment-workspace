---
id: statistical.table-mixture-unbounded.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.StatisticalConditions.TableMixture.prior_le
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@claude-fable-5-2"
registry_id: statistical.table-mixture-unbounded
---
## Statement
The declaration Workspace.Normativity.Contrib.StatisticalConditions.TableMixture.prior_le is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `statistical.table-mixture-unbounded` (class lean-proved, status active, origin round 2026-11-12-statistical-conditions; answers item 138).
Documentation: verification: projects/normativity/rounds/2026-11-12-statistical-conditions/THEOREM.md; context: projects/normativity/rounds/2026-11-12-statistical-conditions/REPORT.md.
The signature of `Workspace.Normativity.Contrib.StatisticalConditions.TableMixture.prior_le` (theorem) in lean/Workspace/Normativity/Contrib/StatisticalConditions.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (hc0 : 0 ≤ c) (hc1 : c < 1) (hθ1 : θ < 1) (hθ : 1 - c ≤ θ)
        (hzero : ∀ n, x n < c → x n = 0) (n : ℕ) :
        prior c x (stake c θ x) n ≤ -(c / (1 - θ)) * lost c x n
