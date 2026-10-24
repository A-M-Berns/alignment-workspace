---
id: kernel.box3-gap-exchange-rate.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Headline.box3_gap_exchange_rate
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: kernel.box3-gap-exchange-rate
---
## Statement
The declaration Workspace.Deference.Headline.box3_gap_exchange_rate is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `kernel.box3-gap-exchange-rate` (class lean-proved, status active, origin round 2026-09-27-corrigibility-kernel-phase2; answers item 104).
Documentation: verification: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md; context: prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md.
The signature of `Workspace.Deference.Headline.box3_gap_exchange_rate` (theorem) in lean/Workspace/Deference/Spec/Headline.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (V₀ g c p : ℝ) (hV : 0 ≤ V₀) (hc : c ≤ B.whi) (hg : 0 < g)
        (hp : 0 ≤ p) :
        (V₀ ≤ (1 - p) * (V₀ + g) + p * c ↔ p * (V₀ + g - c) ≤ g) ∧
          (p * (V₀ + g - c) ≤ g → p ≤ g / (g + |B.whi|))
