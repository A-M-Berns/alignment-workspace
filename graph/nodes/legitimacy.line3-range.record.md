---
id: legitimacy.line3-range.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.AccountJoin.ValueChange.line3Old_le_line3
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@claude-fable-5-2"
registry_id: legitimacy.line3-range
---
## Statement
The declaration Workspace.Deference.Contrib.AccountJoin.ValueChange.line3Old_le_line3 is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `legitimacy.line3-range` (class lean-proved, status active, origin round 2026-11-10-legitimacy-definition-prosecution; answers item 137).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/BRIDGE_LEAN.md; context: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN.md.
The signature of `Workspace.Deference.Contrib.AccountJoin.ValueChange.line3Old_le_line3` (theorem) in lean/Workspace/Deference/Contrib/AccountJoin.lean, verbatim, binders included, after the section variables in scope (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    variable {Pol Ω I : Type*} (D : ValueChange Pol Ω I)
    variable [Fintype Pol]

    : D.line3Old ≤ D.line3
