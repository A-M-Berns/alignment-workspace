---
id: delegation.gradetrust-refinement.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.DelegationBridge.gradeTrust_of_refinement
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: delegation.gradetrust-refinement
---
## Statement
The declaration Workspace.Deference.Contrib.DelegationBridge.gradeTrust_of_refinement is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `delegation.gradetrust-refinement` (class lean-proved, status active, origin round 2026-08-11-phase-ii-promotion; answers item 23).
Documentation: verification: prompts/2026-08-11-phase-ii-promotion/REPORT.md; context: prompts/2026-08-11-deference-finite-kernel/REPORT.md.
The signature of `Workspace.Deference.Contrib.DelegationBridge.gradeTrust_of_refinement` (theorem) in lean/Workspace/Deference/Contrib/DelegationBridge.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    [DecidableEq C] {Cf : Type*} [Fintype Cf] (r : Cf → C)
        (q : Cf → ℚ) (EXf Wf : Cf → P → ℚ) (EXc Wc : C → P → ℚ) (η : ℚ)
        (hq : ∀ y, 0 ≤ q y)
        (hsum : ∀ x : C, ∑ y ∈ univ.filter (fun y => r y = x), q y = 1)
        (hEX : ∀ (x : C) (π : P), EXc x π = ∑ y ∈ univ.filter (fun y => r y = x), q y * EXf y π)
        (hW : ∀ (y : Cf) (π : P), Wf y π = Wc (r y) π)
        (hfine : GradeTrust EXf Wf η) :
        GradeTrust EXc Wc η
