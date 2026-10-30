---
id: shortfall.deferred-eventually-excluded.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.ShortfallSecurity.deferred_eventually_excluded
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: shortfall.deferred-eventually-excluded
---
## Statement
The declaration Workspace.Deference.Contrib.ShortfallSecurity.deferred_eventually_excluded is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `shortfall.deferred-eventually-excluded` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/FOLLOWUP.md.
The signature of `Workspace.Deference.Contrib.ShortfallSecurity.deferred_eventually_excluded` (theorem) in lean/Workspace/Deference/Contrib/ShortfallSecurity.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    [IsLogicalInductor P (DP.union (shortfallProcess short defer))] {k : ℕ} [DecidableEq (Fin k)]
        (idx : Fin k → ℕ) (G : GateParams (Fin k)) (hθ : G.θlo < G.θhi) (hθ1 : G.θhi < 1)
        (pT b : ℕ → Fin k → ℝ) (pref : Fin k → ℝ) (j : Fin k) (hj : j ∉ G.Inq)
        (hs : short (idx j) = true)
        (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP.union (shortfallProcess short defer)).D n)) :
        ∃ N, ∀ n, N ≤ n →
          cgate G (fun a => P n (shortAtom (idx a))) (pT n) (b n) pref j = 0
