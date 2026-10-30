---
id: authorship.mediation-by-reexecution.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.EvaluationEcosystem.reasonMediated_of_reexecution
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: authorship.mediation-by-reexecution
---
## Statement
The declaration Workspace.Deference.Contrib.EvaluationEcosystem.reasonMediated_of_reexecution is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `authorship.mediation-by-reexecution` (class lean-proved, status active, origin round 2026-09-10-committed-principal-program; answers item 87).
Documentation: verification: projects/deference/rounds/2026-09-10-committed-principal-program/PRINCIPAL_PROGRAM.md; context: prompts/2026-09-10-committed-principal-program/REPORT.md.
The signature of `Workspace.Deference.Contrib.EvaluationEcosystem.reasonMediated_of_reexecution` (theorem) in lean/Workspace/Deference/Contrib/EvaluationEcosystem.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {Q Z : Type*} (β : Q → Z → Log) (D : Set Q) (z : Z)
        (π : Prog) (o : ℕ) (hπ : ∀ q ∈ D, progOf (β q z) o = π)
        (hact : ∀ q ∈ D, (payload (β q z) o).isSome) :
        ReasonMediated β (fun log => traceAtCommit log o) (fun log => payload log o) D z
