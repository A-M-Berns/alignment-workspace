---
id: force.deductive-witness.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.DeductiveEnforcement.witness_market_not_exploited
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: force.deductive-witness
---
## Statement
The declaration Workspace.Normativity.Contrib.DeductiveEnforcement.witness_market_not_exploited is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `force.deductive-witness` (class lean-proved, status active, origin round 2026-08-16-traderized-enforcement; answers item 41).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-16-traderized-enforcement/DEDUCTION_SPECIAL_CASE.md.
The signature of `Workspace.Normativity.Contrib.DeductiveEnforcement.witness_market_not_exploited` (theorem) in lean/Workspace/Normativity/Contrib/DeductiveEnforcement.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (Tr : Trader) (hTr : EfficientlyComputable Tr) :
        ¬ Tr.Exploits (history witnessProcess witnessEnforcer) witnessProcess
