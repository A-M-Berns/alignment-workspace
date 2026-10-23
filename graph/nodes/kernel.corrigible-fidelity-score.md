---
id: kernel.corrigible-fidelity-score
kind: and
children: [kernel.corrigible-fidelity-score.record, kernel.corrigible-fidelity-score.bridge, kernel.corrigible-fidelity-score.complete]
work: [{kind: round, ref: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2}, {kind: priorities, ref: 104}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
`Headline.Corrigible U D′ lo ϖ′` is the preference property over recognized violations (window `D′ − ϖ′ < lo`; the known clause with the margin `ϖ′ − (D′ − lo)`; the risk clause at the exchange rate). The evaluation form `bid − ϖ n − ϖ p` at `D`, `w`, `ϖ` has it.

## Source
projects/deference/CLAIMS.md, entry `kernel.corrigible-fidelity-score` (class lean-proved, status active, origin round 2026-09-27-corrigibility-kernel-phase2; answers item 104).
Documentation: verification: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md; context: prompts/2026-09-27-corrigibility-kernel-phase2/FOLLOWUP.md.
The signature of `Workspace.Deference.Headline.fidelityScore_corrigible` in lean/Workspace/Deference/Spec/Headline.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. Registry note: `Headline.Corrigible U D′ lo ϖ′` is the preference property over recognized violations (window `D′ − ϖ′ < lo`; the known clause with the margin `ϖ′ − (D′ − lo)`; the risk clause at the exchange rate). The evaluation form `bid − ϖ n − ϖ p` at `D`, `w`, `ϖ` has it. What it does not say: that the ordinary term is her evaluation (`corrigible_not_aligned` shows it need not be). The registry's `answers_item` is the `priorities` pointer to item 104 (ruling F2).
