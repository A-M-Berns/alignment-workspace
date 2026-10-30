---
id: post.witness-sole-authority.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.EffectiveAuthority.sole_authority_eval_eq
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: post.witness-sole-authority
---
## Statement
The declaration Workspace.Deference.Contrib.EffectiveAuthority.sole_authority_eval_eq is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `post.witness-sole-authority` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.EffectiveAuthority.sole_authority_eval_eq` (theorem) in lean/Workspace/Deference/Contrib/EffectiveAuthority.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (P : LexParams) (k pS pT pS' pT' : ℝ) (h : pS + pT = pS' + pT') :
        P.evalOf k 0 pS pT = P.evalOf k 0 pS' pT'
