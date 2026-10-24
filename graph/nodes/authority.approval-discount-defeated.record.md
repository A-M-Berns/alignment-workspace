---
id: authority.approval-discount-defeated.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.EffectiveAuthority.discount_defeats_exchange_rate
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: authority.approval-discount-defeated
---
## Statement
The declaration Workspace.Deference.Contrib.EffectiveAuthority.discount_defeats_exchange_rate is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `authority.approval-discount-defeated` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.EffectiveAuthority.discount_defeats_exchange_rate` (theorem) in lean/Workspace/Deference/Contrib/EffectiveAuthority.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (P : LexParams) (bid c : ℝ) (hc : c < bid)
        (hw : P.w ≤ c) :
        discounted P bid 1 1 = bid ∧ P.evalOf c 0 0 0 < discounted P bid 1 1 ∧
          (P.D - c) / P.ϖ < 1
