---
id: coherence.modulus-soundness
kind: and
children: [coherence.modulus-soundness.record, coherence.modulus-soundness.bridge, coherence.modulus-soundness.complete]
work: [{kind: round, ref: projects/normativity/rounds/2026-08-16-traderized-enforcement}, {kind: priorities, ref: 42}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
The soundness half of the coherence measure. It does not answer item 42, which asks for a polynomially presentable family; it is the half of the measure item 42's narrowing is stated against.

## Source
projects/normativity/CLAIMS.md, entry `coherence.modulus-soundness` (class lean-proved, status active, origin round 2026-08-16-traderized-enforcement; answers item 42).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-16-traderized-enforcement/PROOF_CLOSURE.md.
The signature of `Workspace.Normativity.Contrib.CoherenceModulus.gap_le_of_mixture` in lean/Workspace/Normativity/Contrib/CoherenceModulus.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. Registry note: The soundness half of the coherence measure. It does not answer item 42, which asks for a polynomially presentable family; it is the half of the measure item 42's narrowing is stated against. The registry's `answers_item` is the `priorities` pointer to item 42 (ruling F2).
