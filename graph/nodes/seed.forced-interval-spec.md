---
id: seed.forced-interval-spec
kind: and
children: [seed.forced-interval-spec.record, seed.forced-interval-spec.bridge, seed.forced-interval-spec.complete]
work: [{kind: round, ref: projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end}, {kind: priorities, ref: 39}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
Fourier-Motzkin elimination of every coordinate but phi computes endpoints that bound P(phi) over the real forced region and are attained there. Rational attainment is item 118.

## Source
projects/normativity/CLAIMS.md, entry `seed.forced-interval-spec` (class lean-proved, status active, origin round 2026-10-21-rebuttal-and-end-to-end; answers item 39).
Documentation: verification: projects/normativity/seed/rounds/2026-09-16-seed-statics/STATICS.md; context: projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/LANDING.md.
The signature of `Workspace.Normativity.Contrib.SeedStatics.forcedInterval_spec` in lean/Workspace/Normativity/Contrib/SeedStatics.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. Registry note: Fourier-Motzkin elimination of every coordinate but phi computes endpoints that bound P(phi) over the real forced region and are attained there. Rational attainment is item 118. The registry's `answers_item` is the `priorities` pointer to item 39 (ruling F2).
