---
id: post.theorem.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.PostStatement.post_theorem
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: post.theorem
---
## Statement
The declaration Workspace.Deference.Contrib.PostStatement.post_theorem is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `post.theorem` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.PostStatement.post_theorem` (theorem) in lean/Workspace/Deference/Contrib/PostStatement.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {Q M Res Disc : Type*} [DecidableEq M] (H : PostHypotheses Q M Res Disc) :
        ((∀ a, H.Viol a = true → H.eval a < H.eval H.queue) ∧
          (∀ a, H.eval H.queue ≤ H.eval a → H.nKnown a = 0 ∧ H.p a ≤ (H.P.D - H.c) / H.P.ϖ)) ∧
        (∀ {X : Type} [Fintype X] (μ : X → ℝ), (∀ x, 0 ≤ μ x) →
          ∀ (ordT ordπ nπ : X → ℝ) (viol : X → Bool),
            (∀ x, viol x = false → ordT x = ordπ x ∧ nπ x = 0) →
            (∀ x, viol x = true → 1 ≤ nπ x ∧ H.P.w ≤ ordT x ∧ ordπ x ≤ H.P.D) →
            expectR μ (fun x => score H.P.ϖ (ordT x) 0)
                - expectR μ (fun x => score H.P.ϖ (ordπ x) (nπ x))
              ≥ (H.P.ϖ - (H.P.D - H.P.w)) * expectR μ (fun x => indR (viol x)))
