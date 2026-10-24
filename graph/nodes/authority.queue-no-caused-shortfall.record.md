---
id: authority.queue-no-caused-shortfall.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.EffectiveAuthority.queue_no_caused_shortfall
hypotheses: [authority.queue-no-caused-shortfall.h-queue-move]
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: authority.queue-no-caused-shortfall
---
## Statement
The declaration Workspace.Deference.Contrib.EffectiveAuthority.queue_no_caused_shortfall is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `authority.queue-no-caused-shortfall` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.EffectiveAuthority.queue_no_caused_shortfall` (theorem) in lean/Workspace/Deference/Contrib/EffectiveAuthority.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (J : AuthAlloc M R Disc) (Adm : ℕ → C → Prop) (cost : C → ℝ)
        (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) (z : ℕ → Z) (m : M)
        (hq : QueueMove I π τ t) : ¬ CausedShortfall I J Adm cost π τ t z m
## Notes
Filed by the map-as-canonical round from the registry entry and the declaration's signature; its hypotheses were unread (ruling F1, 2026-10-23) until the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice) filed 1 hypothesis leaf by reading the declaration. The signature stays in the Source as the text they were read from.
