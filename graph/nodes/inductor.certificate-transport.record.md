---
id: inductor.certificate-transport.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.bracket_at_market
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: inductor.certificate-transport
---
## Statement
The declaration Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.bracket_at_market is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `inductor.certificate-transport` (class lean-proved, status active, origin round 2026-10-22-normative-inductor-integration; answers item 124).
Documentation: verification: projects/normativity/rounds/2026-10-22-normative-inductor-integration/THEOREM_STORY.md; context: projects/normativity/rounds/2026-10-22-normative-inductor-integration/HANDOFFS.md.
The signature of `Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.bracket_at_market` (theorem) in lean/Workspace/Normativity/Contrib/WarrantForce.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (n : ℕ) (y : Fin d → ℚ) (hy : (W.bundle n).Region y)
        {m m' : ℕ} {φ : Fin d} {v : ℚ} {c : VerdictCert d m m' φ}
        (hsupp : SupportedOn (W.bundle n) φ v c) :
        -c.lo.value - c.lo.mass * W.tol n ≤ W.priceVec DP n φ ∧
          W.priceVec DP n φ ≤ c.hi.value + c.hi.mass * W.tol n
