---
id: smoke.faf-asymp-refl.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Smoke.faf_asympEq_refl
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: smoke.faf-asymp-refl
---
## Statement
The declaration Workspace.Smoke.faf_asympEq_refl is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `smoke.faf-asymp-refl` (class lean-proved, status active, origin round 2026-08-10-repo-scaffolding; answers item 13).
Documentation: verification: prompts/2026-08-10-repo-scaffolding/REPORT.md; context: README.md.
The signature of `Workspace.Smoke.faf_asympEq_refl` (theorem) in lean/Workspace/Smoke.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (f : ℕ → ℝ) : AsympEq f f
