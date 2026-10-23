---
id: li.assessment.budgeter-value.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.AssessmentProcess.BudgeterAt_value_eq_of_safe
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: li.assessment.budgeter-value
---
## Statement
The statement of record of `li.assessment.budgeter-value` is accepted by the Lean kernel in the repository's Lean library; the declaration is named in the Source.

## Source
projects/normativity/CLAIMS.md, entry `li.assessment.budgeter-value` (class lean-proved, status active, origin round 2026-08-16-traderized-enforcement; answers item 47).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-16-traderized-enforcement/THEOREM_MAP.md.
The signature of `Workspace.Normativity.Contrib.AssessmentProcess.BudgeterAt_value_eq_of_safe` (theorem) in lean/Workspace/Normativity/Contrib/AssessmentProcess.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (L : Assessment) (Tr : Trader) (b : ℕ)
        (hb : 0 < b) (P : History) (Q : ℕ → Sentence → ℚ) (n : ℕ)
        (hQ : ∀ day, day < n → ∀ φ, P day φ = (Q day φ : ℝ))
        (hsafe : ∀ m, m ≤ n → ∀ v : PCWorld, L.Live m v → -(b : ℝ) < Tr.netWorth P v m)
        (w : Sentence → ℝ) :
        (BudgeterAt L Tr b Q n).value P w = (Tr.strat n).value P w
