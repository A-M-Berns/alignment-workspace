---
id: authority.approval-discount-defeated.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.EffectiveAuthority.discount_defeats_exchange_rate
hypotheses: [authority.approval-discount-defeated.h-case]
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
## Notes
Filed by the map-as-canonical round from the registry entry and the declaration's signature; its hypotheses were unread (ruling F1, 2026-10-23) until the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice) filed 1 hypothesis leaf by reading the declaration. The signature stays in the Source as the text they were read from.
