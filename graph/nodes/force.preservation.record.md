---
id: force.preservation.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.EnforcementPreservation.no_efficient_trader_exploits
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: force.preservation
---
## Statement
The declaration Workspace.Normativity.Contrib.EnforcementPreservation.no_efficient_trader_exploits is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `force.preservation` (class lean-proved, status active, origin round 2026-08-16-traderized-enforcement; answers item 41).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-16-traderized-enforcement/FUNDING_AND_SAFETY.md.
The signature of `Workspace.Normativity.Contrib.EnforcementPreservation.no_efficient_trader_exploits` (theorem) in lean/Workspace/Normativity/Contrib/EnforcementPreservation.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (L : Assessment) (E : AdaptiveTrader) (B : ℝ)
        (hliab : ∀ n (v : PCWorld), L.Live n v →
          -B ≤ (realizedEnforcer L E).netWorth (history L E) v n)
        (Tr : Trader) (hTr : EfficientlyComputable Tr) :
        ¬ L.Exploits Tr (history L E)
