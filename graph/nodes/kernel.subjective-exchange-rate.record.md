---
id: kernel.subjective-exchange-rate.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Headline.subjective_exchange_rate
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: kernel.subjective-exchange-rate
---
## Statement
The declaration Workspace.Deference.Headline.subjective_exchange_rate is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `kernel.subjective-exchange-rate` (class lean-proved, status active, origin round 2026-09-27-corrigibility-kernel-phase2; answers item 104).
Documentation: verification: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md; context: prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md.
The signature of `Workspace.Deference.Headline.subjective_exchange_rate` (theorem) in lean/Workspace/Deference/Spec/Headline.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (P : LexParams) (bid : ℝ) (hb : bid ≤ P.D) (nKnown : ℕ)
        (pS pT : ℝ) (hp : 0 ≤ pS + pT) (c : ℝ) (hc : P.w ≤ c)
        (hpref : P.evalOf c 0 0 0 ≤ P.evalOf bid nKnown pS pT) :
        nKnown = 0 ∧ pS + pT ≤ (P.D - c) / P.ϖ
