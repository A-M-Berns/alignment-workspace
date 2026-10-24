---
id: post.flood-below-asking.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.PostStatement.PostHypotheses.flood_below_asking
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: post.flood-below-asking
---
## Statement
The declaration Workspace.Deference.Contrib.PostStatement.PostHypotheses.flood_below_asking is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `post.flood-below-asking` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/FOLLOWUP.md.
The signature of `Workspace.Deference.Contrib.PostStatement.PostHypotheses.flood_below_asking` (theorem) in lean/Workspace/Deference/Contrib/PostStatement.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (a : Q)
        (ha : Workspace.Deference.Contrib.EffectiveAuthority.asksDeviate H.pr H.pool (H.asks a) = true) :
        H.eval a < H.eval H.queue
