---
id: authority.comprehension-short.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.EffectiveAuthority.comprehension_short
hypotheses: [authority.comprehension-short.h-cost-table, authority.comprehension-short.h-calm-exterior, authority.comprehension-short.h-case]
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: authority.comprehension-short
---
## Statement
The declaration Workspace.Deference.Contrib.EffectiveAuthority.comprehension_short is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `authority.comprehension-short` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.EffectiveAuthority.comprehension_short` (theorem) in lean/Workspace/Deference/Contrib/EffectiveAuthority.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (J : AuthAlloc M R Disc) (Adm : ℕ → C → Prop) (base : C → ℝ)
        (hbase : ∀ c, 0 ≤ base c) (lam compr : ℝ) (hlam : 0 ≤ lam) (p : ℕ) (t : ℕ) (z : ℕ → Z)
        (henv : ∀ n x, I.env (z n) x = x) (x : S) (m : M) (hres : J.Reserved m)
        (costBound_nonneg : 0 ≤ (J.entry m).costBound) (hbound : (J.entry m).costBound < compr)
        (r : R) (hr : r ∈ (J.entry m).required) (hφ : ¬ I.φ r x) :
        Short I J Adm (attnCost base lam p compr) t z x m
## Notes
Filed by the map-as-canonical round from the registry entry and the declaration's signature; its hypotheses were unread (ruling F1, 2026-10-23) until the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice) filed 3 hypothesis leafves by reading the declaration. The signature stays in the Source as the text they were read from.
