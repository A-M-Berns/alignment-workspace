---
id: shortfall.deferred-ahead.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.ShortfallSecurity.deferred_ahead
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: shortfall.deferred-ahead
---
## Statement
The declaration Workspace.Deference.Contrib.ShortfallSecurity.deferred_ahead is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `shortfall.deferred-ahead` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/FOLLOWUP.md.
The signature of `Workspace.Deference.Contrib.ShortfallSecurity.deferred_ahead` (theorem) in lean/Workspace/Deference/Contrib/ShortfallSecurity.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    [IsLogicalInductor P (DP.union (shortfallProcess short defer))] (a : ℕ → ℕ)
        {c : Nat.Partrec.Code} (ha : PolyFueled c a) (hshort : ∀ n, short (a n) = true)
        (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP.union (shortfallProcess short defer)).D n))
        (hdefer : ∀ n, n < defer (a n)) (θ : ℝ) (hθ : θ < 1) :
        (∀ n, shortAtom (a n) ∉ (shortfallProcess short defer).D n) ∧
          ∃ N, ∀ n, N ≤ n → θ ≤ P n (shortAtom (a n))
