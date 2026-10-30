---
id: integrity.receipts-immutable.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.terminals_subst
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: integrity.receipts-immutable
---
## Statement
The declaration Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.terminals_subst is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `integrity.receipts-immutable` (class lean-proved, status active, origin round 2026-09-06-mathematical-consolidation; answers item 78).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/THEOREMS.md; context: projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/CONSOLIDATION.md.
The signature of `Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.terminals_subst` (theorem) in lean/Workspace/Normativity/Contrib/OccurrenceIntegrity.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (hab : A.history <+: B.history)
        (replacement : (p : Fin A.portCount) → Program S B (A.demand p))
        (t : Program S A r) :
        (t.subst hab replacement).terminals =
          t.terminals + (t.livePorts.map fun p => (replacement p).terminals).sum
