---
id: post.witness-learned-weight.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.EffectiveAuthority.learned_weight_no_guarantee_at
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: post.witness-learned-weight
---
## Statement
The declaration Workspace.Deference.Contrib.EffectiveAuthority.learned_weight_no_guarantee_at is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `post.witness-learned-weight` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.EffectiveAuthority.learned_weight_no_guarantee_at` (theorem) in lean/Workspace/Deference/Contrib/EffectiveAuthority.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (D : ℝ) (hD : 0 < D) (N : ℕ) (hN : 1 ≤ N) :
        empiricalWeight (delayedStream D N) N = 0 ∧
          score (empiricalWeight (delayedStream D N) N) 0 0
            ≤ score (empiricalWeight (delayedStream D N) N) D 1 ∧
          ∀ n, 2 * N < n → D < empiricalWeight (delayedStream D N) n ∧
            score (empiricalWeight (delayedStream D N) n) D 1
              < score (empiricalWeight (delayedStream D N) n) 0 0
