---
id: authority.flood-caused-shortfall.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.EffectiveAuthority.flood_raises_pending
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: authority.flood-caused-shortfall
---
## Statement
The declaration Workspace.Deference.Contrib.EffectiveAuthority.flood_raises_pending is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `authority.flood-caused-shortfall` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.EffectiveAuthority.flood_raises_pending` (theorem) in lean/Workspace/Deference/Contrib/EffectiveAuthority.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (J : AuthAlloc M R Disc) (Adm : ℕ → C → Prop) (base : C → ℝ)
        (lam compr : ℝ) (hlam : 0 ≤ lam) (pIdle pAgent : ℕ) (t : ℕ) (z : ℕ → Z) (x : S) (m : M)
        (h : FloodShortfall I J Adm base lam compr pIdle pAgent t z x m) : pIdle < pAgent
