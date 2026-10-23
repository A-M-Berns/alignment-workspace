---
id: deconfusing.theorem2b.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.DeconfusingCorrigibility.Decision.theorem2b
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: deconfusing.theorem2b
---
## Statement
The declaration Workspace.Deference.Contrib.DeconfusingCorrigibility.Decision.theorem2b is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `deconfusing.theorem2b` (class lean-proved, status active, origin round 2026-10-17-post-companion-formalization; answers item 107).
Documentation: verification: prompts/2026-10-17-post-companion-formalization/REPORT.md; context: prompts/2026-10-17-post-companion-formalization/PROMPT.md; companion: wiki/Deconfusing-Corrigibility-Companion.md.
The signature of `Workspace.Deference.Contrib.DeconfusingCorrigibility.Decision.theorem2b` (theorem) in lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (a astar : A) (hstar : D.Respects astar) :
        D.U astar - D.U a ≥ (D.lam - (1 + D.δ)) * D.v a - D.κ a astar
