---
id: exact.floor-market.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.ExactConditions.FloorSchedule.exists_market
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@claude-fable-5-2"
registry_id: exact.floor-market
---
## Statement
The declaration Workspace.Normativity.Contrib.ExactConditions.FloorSchedule.exists_market is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `exact.floor-market` (class lean-proved, status active, origin round 2026-11-10-exact-conditions-capital; answers item 136).
Documentation: verification: projects/normativity/rounds/2026-11-10-exact-conditions-capital/THEOREM.md; context: projects/normativity/rounds/2026-11-10-exact-conditions-capital/REPORT.md.
The signature of `Workspace.Normativity.Contrib.ExactConditions.FloorSchedule.exists_market` (theorem) in lean/Workspace/Normativity/Contrib/ExactConditionsFloor.lean, verbatim, with the namespace's `variable (F : FloorSchedule) (L : Assessment)` written as binders (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (F : FloorSchedule) (L : Assessment) :
        ∃ M : DualCertifiedMarket, M.L = L ∧ M.C = floors F.φ F.c ∧ M.U = 3
