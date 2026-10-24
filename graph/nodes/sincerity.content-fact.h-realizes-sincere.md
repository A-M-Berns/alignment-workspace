---
id: sincerity.content-fact.h-realizes-sincere
kind: leaf
leaf_kind: hypothesis
discharge: open
author: "@smithy-verity"
size: S
size_reason: "one hypothesis of the declaration, read"
version: 1
---
## Statement
The utterance channel realizes the sincere reference on the speaker's belief over the domain: what the speaker says is what the speaker believes, as a property of the speaker's actual policy.

## Source
projects/deference/CLAIMS.md, entry `sincerity.content-fact` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
The signature in lean/Workspace/Deference/Contrib/Sincerity.lean, read by the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice); projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md, Parts B and C.

## Notes
The binder `h : Realizes β b f (sincere) D`. Open: the identity holds exactly under it, and a lying policy fails it (`Witness.lying_policy`); the comparison is with the speaker's actual policy, not her beliefs about it, so nothing in the record discharges it.
