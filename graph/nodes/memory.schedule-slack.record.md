---
id: memory.schedule-slack.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.Forgetting.schedule_slack
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: memory.schedule-slack
---
## Statement
The declaration Workspace.Normativity.Contrib.Forgetting.schedule_slack is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `memory.schedule-slack` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 135).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.Forgetting.schedule_slack` (theorem) in lean/Workspace/Normativity/Contrib/Forgetting.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (K K₀ : ∀ t, Recollection (n (t + 1)) (n t))
        (B : ∀ t, Finset (Fin (n t))) (hB : ∀ t w, w ∉ B t → (K t).k w = (K₀ t).k w) (lo hi : ℚ)
        (q : Fin (n 0) → ℚ) (hq : ∀ w, 0 ≤ q w) :
        ∀ T (r : Row (n T)), (∀ i, lo ≤ r.a i ∧ r.a i ≤ hi) →
          excess r ((chain K T).push q) ≤
            excess r ((chain K₀ T).push q) + (hi - lo) * scheduleLoss K B q T
