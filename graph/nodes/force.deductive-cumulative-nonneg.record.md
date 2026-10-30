---
id: force.deductive-cumulative-nonneg.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.DeductiveEnforcement.enforcement_netWorth_nonneg
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: force.deductive-cumulative-nonneg
---
## Statement
The declaration Workspace.Normativity.Contrib.DeductiveEnforcement.enforcement_netWorth_nonneg is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `force.deductive-cumulative-nonneg` (class lean-proved, status active, origin round 2026-08-16-traderized-enforcement; answers item 41).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-16-traderized-enforcement/DEDUCTION_SPECIAL_CASE.md.
The signature of `Workspace.Normativity.Contrib.DeductiveEnforcement.enforcement_netWorth_nonneg` (theorem) in lean/Workspace/Normativity/Contrib/DeductiveEnforcement.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (DP : DeductiveProcess) (E : AdaptiveTrader)
        (hday : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
          0 ≤ ((realizedEnforcer DP E).strat n).value (history DP E) v.payout)
        (n : ℕ) (v : PCWorld) (hv : v.ConsistentWith (DP.D n)) :
        0 ≤ (realizedEnforcer DP E).netWorth (history DP E) v n
