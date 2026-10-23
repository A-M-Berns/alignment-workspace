---
id: deconfusing.theorem1.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.DeconfusingCorrigibility.Scoring.theorem1
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: deconfusing.theorem1
---
## Statement
The declaration Workspace.Deference.Contrib.DeconfusingCorrigibility.Scoring.theorem1 is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `deconfusing.theorem1` (class lean-proved, status active, origin round 2026-10-17-post-companion-formalization; answers item 107).
Documentation: verification: prompts/2026-10-17-post-companion-formalization/REPORT.md; context: prompts/2026-10-17-post-companion-formalization/PROMPT.md; companion: wiki/Deconfusing-Corrigibility-Companion.md.
The signature of `Workspace.Deference.Contrib.DeconfusingCorrigibility.Scoring.theorem1` (theorem) in lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (h : H) :
        ((1 ≤ Sc.N h → Sc.S h ≤ 1 - Sc.lam) ∧ 1 - Sc.lam < -Sc.δ) ∧
          (Sc.N h = 0 ∧ ¬ Sc.Legit h → -Sc.δ ≤ Sc.S h ∧ Sc.S h < 0) ∧
          (Sc.N h = 0 ∧ Sc.Legit h → 0 ≤ Sc.S h ∧ Sc.S h ≤ 1)
