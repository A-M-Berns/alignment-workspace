---
id: exact.seller-obstruction.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.ExactConditions.Condition.seller_exploits
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@claude-fable-5-2"
registry_id: exact.seller-obstruction
---
## Statement
The declaration Workspace.Normativity.Contrib.ExactConditions.Condition.seller_exploits is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `exact.seller-obstruction` (class lean-proved, status active, origin round 2026-11-10-exact-conditions-capital; answers item 137).
Documentation: verification: projects/normativity/rounds/2026-11-10-exact-conditions-capital/THEOREM.md; context: projects/normativity/rounds/2026-11-10-exact-conditions-capital/REPORT.md.
The signature of `Workspace.Normativity.Contrib.ExactConditions.Condition.seller_exploits` (theorem) in lean/Workspace/Normativity/Contrib/ExactConditions.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (L : Assessment) (w : ℕ → ℕ → ℚ) (hw : ∀ n j, 0 ≤ w n j)
        (P : History) (hmem : ∀ n, C.Holds n (P n)) (Ub : ℝ)
        (hub : ∀ N v, L.Live N v → C.account (fun n j => (w n j : ℝ)) N v.payout ≤ Ub)
        (hunb : ∀ B : ℝ, ∃ N v, L.Live N v ∧
          C.account (fun n j => (w n j : ℝ)) N v.payout < -B) :
        L.Exploits (C.seller w) P
