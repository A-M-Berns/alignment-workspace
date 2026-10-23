---
id: kernel.corrigible-generic.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Headline.generic_corrigible
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: kernel.corrigible-generic
---
## Statement
The declaration Workspace.Deference.Headline.generic_corrigible is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `kernel.corrigible-generic` (class lean-proved, status active, origin round 2026-09-27-corrigibility-kernel-phase2; answers item 104).
Documentation: verification: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md; context: prompts/2026-09-27-corrigibility-kernel-phase2/FOLLOWUP.md.
The signature of `Workspace.Deference.Headline.generic_corrigible` (theorem) in lean/Workspace/Deference/Spec/Headline.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (ϖ' D' lo : ℝ) (hD : 0 ≤ D') (hlo : lo ≤ 0) (hwin : D' - ϖ' < lo) :
        Corrigible (fun o n p => score ϖ' o n - ϖ' * p) D' lo ϖ'
