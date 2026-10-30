---
id: force.strategy-value.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.EnforcementStrategy.marketValueRat_enforcementStrategy
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: force.strategy-value
---
## Statement
The declaration Workspace.Normativity.Contrib.EnforcementStrategy.marketValueRat_enforcementStrategy is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `force.strategy-value` (class lean-proved, status active, origin round 2026-08-16-traderized-enforcement; answers item 41).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-16-traderized-enforcement/ENFORCEMENT.md.
The signature of `Workspace.Normativity.Contrib.EnforcementStrategy.marketValueRat_enforcementStrategy` (theorem) in lean/Workspace/Normativity/Contrib/EnforcementStrategy.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (pres : Presentation) (n : ℕ)
        (Q : ℕ → Sentence → ℚ) (w : Sentence → ℚ) :
        (enforcementStrategy pres n).marketValueRat Q w =
          pair pres.coords (pres.compiledPosition (Q n)) (fun φ => w φ - Q n φ)
