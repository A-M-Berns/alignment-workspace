---
id: kernel.box2-dominance.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Headline.box2_dominance
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: kernel.box2-dominance
---
## Statement
The declaration Workspace.Deference.Headline.box2_dominance is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `kernel.box2-dominance` (class lean-proved, status active, origin round 2026-09-27-corrigibility-kernel-phase2; answers item 104).
Documentation: verification: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md; context: prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md.
The signature of `Workspace.Deference.Headline.box2_dominance` (theorem) in lean/Workspace/Deference/Spec/Headline.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (ϖ D wlo : ℝ) (hϖ0 : 0 ≤ ϖ)
        (ordT ordπ nπ : X → ℝ) (viol : X → Bool)
        (hagree : ∀ x, viol x = false → ordT x = ordπ x ∧ nπ x = 0)
        (hviol : ∀ x, viol x = true → 1 ≤ nπ x ∧ wlo ≤ ordT x ∧ ordπ x ≤ D) :
        expectR μ (fun x => score ϖ (ordT x) 0) - expectR μ (fun x => score ϖ (ordπ x) (nπ x))
          ≥ (ϖ - (D - wlo)) * expectR μ (fun x => indR (viol x))
