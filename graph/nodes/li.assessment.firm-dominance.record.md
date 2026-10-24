---
id: li.assessment.firm-dominance.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.AssessmentFirm.trading_firm_dominance
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: li.assessment.firm-dominance
---
## Statement
The declaration Workspace.Normativity.Contrib.AssessmentFirm.trading_firm_dominance is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `li.assessment.firm-dominance` (class lean-proved, status active, origin round 2026-08-16-traderized-enforcement; answers item 47).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-16-traderized-enforcement/THEOREM_MAP.md.
The signature of `Workspace.Normativity.Contrib.AssessmentFirm.trading_firm_dominance` (theorem) in lean/Workspace/Normativity/Contrib/AssessmentFirm.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (L : Assessment) (P : History)
        (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1) (Q : ℕ → Sentence → ℚ)
        (hQ : ∀ day φ, P day φ = (Q day φ : ℝ)) (Tr : Trader)
        (hTr : EfficientlyComputable Tr) (hEx : L.Exploits Tr P) :
        L.Exploits (tradingFirmTrader L Q) P
