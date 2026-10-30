---
id: transparent.blind-payload.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.TransparentChannel.blind_payload_of_realizes
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: transparent.blind-payload
---
## Statement
The declaration Workspace.Deference.Contrib.TransparentChannel.blind_payload_of_realizes is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `transparent.blind-payload` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.TransparentChannel.blind_payload_of_realizes` (theorem) in lean/Workspace/Deference/Contrib/TransparentChannel.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (β : Q → Z → Ω) (x : Ω → X) (R : Ω → ℛ) (V : Ω → 𝒱)
        (κ : X → Z → ℛ) (D : Set Q) (P : Set (Q × Q)) (z : Z) (hP : ∀ p ∈ P, p.1 ∈ D ∧ p.2 ∈ D)
        (hx : Blind β x P z) (hR : Realizes β x R κ D) (hM : ReasonMediated β R V D z) :
        Blind β V P z
