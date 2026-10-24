---
id: certificate.override-bound.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.CertificateBounds.override_bound
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: certificate.override-bound
---
## Statement
The declaration Workspace.Deference.Contrib.CertificateBounds.override_bound is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `certificate.override-bound` (class lean-proved, status active, origin round 2026-08-11-phase-ii-promotion; answers item 23).
Documentation: verification: prompts/2026-08-11-phase-ii-promotion/REPORT.md; context: prompts/2026-08-11-deference-certificates/REPORT.md.
The signature of `Workspace.Deference.Contrib.CertificateBounds.override_bound` (theorem) in lean/Workspace/Deference/Contrib/CertificateBounds.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {p η : Ω → ℚ} {v vh : Ω → P → ℚ} {J : Ω → P} {j : P}
        {S : Finset Ω} {γ ε : ℚ}
        (hp : ∀ ω, 0 ≤ p ω) (hη : ∀ ω, 0 ≤ η ω)
        (herr : ∀ ω π, |v ω π - vh ω π| ≤ η ω)
        (hmargin : ∀ ω ∈ S, ∀ π, π ≠ j → vh ω π + γ ≤ vh ω j)
        (hJ : ∀ ω π, v ω π ≤ v ω (J ω))
        (hγ : 0 < γ)
        (hTR : ∑ ω, p ω * η ω ≤ ε) :
        ∑ ω ∈ S.filter (fun ω => J ω ≠ j), p ω ≤ 2 * ε / γ
