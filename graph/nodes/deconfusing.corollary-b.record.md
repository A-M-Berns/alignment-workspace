---
id: deconfusing.corollary-b.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.DeconfusingCorrigibility.Exploration.corollary_b
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: deconfusing.corollary-b
---
## Statement
The declaration Workspace.Deference.Contrib.DeconfusingCorrigibility.Exploration.corollary_b is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `deconfusing.corollary-b` (class lean-proved, status active, origin round 2026-10-17-post-companion-formalization; answers item 107).
Documentation: verification: prompts/2026-10-17-post-companion-formalization/REPORT.md; context: prompts/2026-10-17-post-companion-formalization/PROMPT.md; companion: wiki/Deconfusing-Corrigibility-Companion.md.
The signature of `Workspace.Deference.Contrib.DeconfusingCorrigibility.Exploration.corollary_b` (theorem) in lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (huff : X.UnbiasedFromFeedback) (a' : ℕ → A)
        (ha' : ∀ k, X.avail k (a' k)) :
        LimsupLE (fun K => X.excess a' K - X.ε K * (X.lam * (X.τ + X.θ))) 0
