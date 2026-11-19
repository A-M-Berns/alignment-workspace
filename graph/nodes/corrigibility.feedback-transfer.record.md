---
id: corrigibility.feedback-transfer.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.AccountJoin.unbiased_of_feedback
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@claude-fable-5-2"
registry_id: corrigibility.feedback-transfer
---
## Statement
The declaration Workspace.Deference.Contrib.AccountJoin.unbiased_of_feedback is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `corrigibility.feedback-transfer` (class lean-proved, status active, origin round 2026-11-10-legitimacy-definition-prosecution; answers item 137).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BRIDGE_LEAN.md; context: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN.md.
The signature of `Workspace.Deference.Contrib.AccountJoin.unbiased_of_feedback` (theorem) in lean/Workspace/Deference/Contrib/AccountJoin.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {A : Type*} (Q : Sequential A) (F : ℕ → ℝ)
        (hF : ∀ γ > 0, ∃ N₀, ∀ K ≥ N₀,
          (∑ k ∈ range K, (Q.U k (Q.a k) - (F k - Q.lam * (Q.N k : ℝ)))) / (K : ℝ) ≤ γ)
        (hgap : LimsupLE (fun K => (∑ k ∈ range K, (F k - Q.V k)) / (K : ℝ)) 0) :
        Q.UnbiasedFromFeedback
