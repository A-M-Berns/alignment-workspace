---
id: substitution.sim-depends-on-induced-choice.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.SubstitutionSeparation.sim_depends_only_on_inducedChoice
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: substitution.sim-depends-on-induced-choice
---
## Statement
The declaration Workspace.Deference.Contrib.SubstitutionSeparation.sim_depends_only_on_inducedChoice is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `substitution.sim-depends-on-induced-choice` (class lean-proved, status active, origin round 2026-08-11-phase-ii-promotion; answers item 23).
Documentation: verification: prompts/2026-08-11-phase-ii-promotion/REPORT.md; context: prompts/2026-08-11-deference-channel/REPORT.md.
The signature of `Workspace.Deference.Contrib.SubstitutionSeparation.sim_depends_only_on_inducedChoice` (theorem) in lean/Workspace/Deference/Contrib/SubstitutionSeparation.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (choice : (P → ℚ) → P) (vh₁ vh₂ X : Ω → P → ℚ)
        (h : inducedSelection choice vh₁ = inducedSelection choice vh₂)
        (crit : (Ω → P) → (Ω → ℚ) → Prop) :
        crit (inducedSelection choice vh₁)
            (realizedQuantity X (inducedSelection choice vh₁))
          ↔ crit (inducedSelection choice vh₂)
            (realizedQuantity X (inducedSelection choice vh₂))
