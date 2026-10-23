---
id: smoke.chain-compiles.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Smoke.chain_compiles
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: smoke.chain-compiles
---
## Statement
The declaration Workspace.Smoke.chain_compiles is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `smoke.chain-compiles` (class lean-proved, status active, origin round 2026-08-10-repo-scaffolding; answers item 13).
Documentation: verification: prompts/2026-08-10-repo-scaffolding/REPORT.md; context: README.md.
The signature of `Workspace.Smoke.chain_compiles` (theorem) in lean/Workspace/Smoke.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    :
        ConvergesTo (fun n : ℕ => (1 : ℝ) / (n + 1)) 0
