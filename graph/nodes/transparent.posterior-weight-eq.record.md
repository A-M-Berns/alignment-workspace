---
id: transparent.posterior-weight-eq.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.TransparentChannel.posterior_weight_eq
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: transparent.posterior-weight-eq
---
## Statement
The declaration Workspace.Deference.Contrib.TransparentChannel.posterior_weight_eq is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `transparent.posterior-weight-eq` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.TransparentChannel.posterior_weight_eq` (theorem) in lean/Workspace/Deference/Contrib/TransparentChannel.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    [DecidableEq Y] (β : Q → Z → Ω) (x : Ω → X) (f : Ω → Y)
        (κ : X → Z → Y) (D : Set Q) (h : Realizes β x f κ D) (μ : Q → Z → ℝ) (y : Y)
        (q : Q) (hq : q ∈ D) (z : Z) :
        μ q z * (if f (β q z) = y then 1 else 0) = μ q z * (if κ (x (β q z)) z = y then 1 else 0)
