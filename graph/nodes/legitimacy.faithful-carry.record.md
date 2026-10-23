---
id: legitimacy.faithful-carry.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.evaluate_subst
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: legitimacy.faithful-carry
---
## Statement
The declaration Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.evaluate_subst is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `legitimacy.faithful-carry` (class lean-proved, status superseded, origin round 2026-09-06-mathematical-consolidation; answers item 78).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/THEOREMS.md; context: projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/CONSOLIDATION.md.
The signature of `Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.evaluate_subst` (theorem) in lean/Workspace/Normativity/Contrib/OccurrenceIntegrity.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (hab : A.history <+: B.history)
        (replacement : (p : Fin A.portCount) → Program S B (A.demand p))
        (t : Program S A r)
        (values : (p : Fin B.portCount) → S.Resolution (B.demand p)) :
        (t.subst hab replacement).evaluate values =
          t.evaluate fun p => (replacement p).evaluate values
