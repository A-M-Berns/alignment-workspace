---
id: exact.prefix-reserve-bound.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.ExactConditions.DualCertifiedMarket.reserve_bound
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@claude-fable-5-2"
registry_id: exact.prefix-reserve-bound
---
## Statement
The declaration Workspace.Normativity.Contrib.ExactConditions.DualCertifiedMarket.reserve_bound is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `exact.prefix-reserve-bound` (class lean-proved, status active, origin round 2026-11-10-exact-conditions-capital; answers item 137).
Documentation: verification: projects/normativity/rounds/2026-11-10-exact-conditions-capital/THEOREM.md; context: projects/normativity/rounds/2026-11-10-exact-conditions-capital/REPORT.md.
The signature of `Workspace.Normativity.Contrib.ExactConditions.DualCertifiedMarket.reserve_bound` (theorem) in lean/Workspace/Normativity/Contrib/ExactConditionsReserve.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {N : ℕ} (R : PrefixReserve M.L M.C N) (ω : R.Ω)
        (hω : 0 < R.r N ω) :
        -(M.U * (1 - R.r N ω) / R.r N ω) ≤ M.C.account M.mu N (R.world ω).payout
