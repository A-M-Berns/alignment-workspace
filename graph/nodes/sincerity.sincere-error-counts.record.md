---
id: sincerity.sincere-error-counts.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.Sincerity.Rows.row20_sincere_counts
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: sincerity.sincere-error-counts
---
## Statement
The declaration Workspace.Deference.Contrib.Sincerity.Rows.row20_sincere_counts is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `sincerity.sincere-error-counts` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.Sincerity.Rows.row20_sincere_counts` (theorem) in lean/Workspace/Deference/Contrib/Sincerity.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    :
        CountedS (lift Rows.row20) state₀ (stAdmit false) ∧
          (Policy.honest.present Rows.decl true).recommend ≠ some Rows.row20.truth ∧
          deviatesS Rows.decl true (Policy.honest.present Rows.decl true) = false
