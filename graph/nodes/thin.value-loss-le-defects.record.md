---
id: thin.value-loss-le-defects.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.ThinLegitimacy.value_loss_le_defects
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: thin.value-loss-le-defects
---
## Statement
The declaration Workspace.Deference.Contrib.ThinLegitimacy.value_loss_le_defects is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `thin.value-loss-le-defects` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.ThinLegitimacy.value_loss_le_defects` (theorem) in lean/Workspace/Deference/Contrib/ThinLegitimacy.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {Act : Type*} [DecidableEq Act] (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w)
        (a m : W → Rec) (F V : Credence W Rec) (u : Act → W → ℝ) (D : ℝ)
        (hD₀ : 0 ≤ D) (hu : ∀ x x' w w', |u x w - u x' w'| ≤ D) (δV δF : Rec → Act)
        (hsel : ∀ r, V r = F r → δV r = δF r) :
        |payoff π (detKernel a) u δV - payoff π (detKernel m) u δF|
          ≤ D * (transparencyDefect π a m + authorshipDefect π a F V)
