---
id: authority.exchange-rate-queue.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.EffectiveAuthority.exchange_rate_queue
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: authority.exchange-rate-queue
---
## Statement
The declaration Workspace.Deference.Contrib.EffectiveAuthority.exchange_rate_queue is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `authority.exchange-rate-queue` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.EffectiveAuthority.exchange_rate_queue` (theorem) in lean/Workspace/Deference/Contrib/EffectiveAuthority.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (P : LexParams) (bid : ℝ) (hb : bid ≤ P.D) (nKnown : ℕ)
        (pS pT : ℝ) (hp : 0 ≤ pS + pT) (cQueue : ℝ) (hc : P.w ≤ cQueue)
        (hpref : P.evalOf cQueue 0 0 0 ≤ P.evalOf bid nKnown pS pT) :
        nKnown = 0 ∧ pS + pT ≤ (P.D - cQueue) / P.ϖ
