---
id: asklist.offprotocol-deviation-finite.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.AskList.offProtocol_deviation_finite
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: asklist.offprotocol-deviation-finite
---
## Statement
The declaration Workspace.Deference.Contrib.AskList.offProtocol_deviation_finite is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `asklist.offprotocol-deviation-finite` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/FOLLOWUP.md.
The signature of `Workspace.Deference.Contrib.AskList.offProtocol_deviation_finite` (theorem) in lean/Workspace/Deference/Contrib/AskListDimension.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (d : Decl3) (p : Pres3) (hdev : deviates3 d p = true)
        (ϖ D ord : ℝ) (n : ℕ) (hD : 0 ≤ D) (hϖ : D < ϖ) (hord : ord ≤ D) :
        score ϖ ord (n + (if deviates3 d p then 1 else 0)) ≤ D - ϖ
