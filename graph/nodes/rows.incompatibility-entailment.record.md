---
id: rows.incompatibility-entailment.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.IncompatibilitySemantics.incEntails_iff_certEntails
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: rows.incompatibility-entailment
---
## Statement
The declaration Workspace.Normativity.Contrib.IncompatibilitySemantics.incEntails_iff_certEntails is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `rows.incompatibility-entailment` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 118).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.IncompatibilitySemantics.incEntails_iff_certEntails` (theorem) in lean/Workspace/Normativity/Contrib/IncompatibilitySemantics.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (Γ : List (Row d)) (g : Row d) :
        IncEntails Γ g ↔ CertEntails Γ g
