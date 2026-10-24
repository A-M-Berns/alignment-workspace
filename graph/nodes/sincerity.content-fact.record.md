---
id: sincerity.content-fact.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.Sincerity.content_fact_eq
hypotheses: [sincerity.content-fact.h-realizes-sincere, sincerity.content-fact.h-setting]
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: sincerity.content-fact
---
## Statement
The declaration Workspace.Deference.Contrib.Sincerity.content_fact_eq is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `sincerity.content-fact` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.Sincerity.content_fact_eq` (theorem) in lean/Workspace/Deference/Contrib/Sincerity.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (β : Q → Z → Ω) (b f : Ω → Y) (D : Set Q)
        (h : Realizes β b f (sincere (Z := Z)) D) (μ : Q → Z → ℝ) (y : Y) (q : Q) (hq : q ∈ D)
        (z : Z) :
        μ q z * (if f (β q z) = y then 1 else 0) = μ q z * (if b (β q z) = y then 1 else 0)
## Notes
Filed by the map-as-canonical round from the registry entry and the declaration's signature; its hypotheses were unread (ruling F1, 2026-10-23) until the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice) filed 2 hypothesis leafves by reading the declaration. The signature stays in the Source as the text they were read from.
