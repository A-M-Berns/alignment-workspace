---
id: legitimacy.payload-of-view.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.Legitimacy.Segment.payload_of_view
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: legitimacy.payload-of-view
---
## Statement
The declaration Workspace.Deference.Contrib.Legitimacy.Segment.payload_of_view is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `legitimacy.payload-of-view` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.Legitimacy.Segment.payload_of_view` (theorem) in lean/Workspace/Deference/Contrib/Legitimacy.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (L : Segment F sem κ O₀ O₁) (z : Z) (q q' : Q) (hq : q ∈ F.D)
        (hq' : q' ∈ F.D) (hx : F.x (F.β q z) = F.x (F.β q' z)) :
        F.V (F.β q z) = F.V (F.β q' z)
