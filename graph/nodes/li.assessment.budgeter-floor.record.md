---
id: li.assessment.budgeter-floor.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.AssessmentProcess.budgetedTrader_netWorth_floor
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: li.assessment.budgeter-floor
---
## Statement
The declaration Workspace.Normativity.Contrib.AssessmentProcess.budgetedTrader_netWorth_floor is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `li.assessment.budgeter-floor` (class lean-proved, status active, origin round 2026-08-16-traderized-enforcement; answers item 47).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-16-traderized-enforcement/THEOREM_MAP.md.
The signature of `Workspace.Normativity.Contrib.AssessmentProcess.budgetedTrader_netWorth_floor` (theorem) in lean/Workspace/Normativity/Contrib/AssessmentProcess.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (L : Assessment) (Tr : Trader) (b : ℕ)
        (hb : 0 < b) (P : History) (Q : ℕ → Sentence → ℚ)
        (hQ : ∀ day φ, P day φ = (Q day φ : ℝ)) :
        ∀ n (v : PCWorld), L.Live n v →
          -(b : ℝ) ≤ (budgetedTrader L Tr b Q).netWorth P v n
