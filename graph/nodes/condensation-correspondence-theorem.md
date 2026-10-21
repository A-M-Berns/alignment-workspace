---
id: condensation-correspondence-theorem
kind: and
children: [condensation-correspondence-theorem.record, condensation-correspondence-theorem.bridge, condensation-shared-givens, condensation-both-perfect, condensation-correspondence-theorem.complete]
author: "@smithy-verity-opus55"
size: M
size_reason: "one theorem, its Lean declaration and its bridge"
version: 1
---
## Statement
Two latent-variable models that both perfectly condense one random-variable
model stand in correspondence: each latent of either model is almost everywhere
a function of the other model's latents above the same given variables.

## Source
projects/deference/faf-cleanroom-2026-10-02/packages/udt-condense-dd/udt-condense-dd-findings.md,
The Eisenstat map: "Theorem 5.2, Exact Correspondence" of the corpus is the
paper's thm:exact-uniq, FAF's "Theorem 4.15
`Condensation.aeFunctionOf_jointAbove_of_perfectlyCondenses`"; the approximate
form is "Theorem 5.8 `Condensation.condEntropy_jointAbove_le`".
projects/deference/faf-cleanroom-2026-10-02/packages/udt-condense-dd/udt-condense-dd-findings.md,
item 6: "Eisenstat's Theorem 4.15 needs perfect condensation of both models".

## Notes
The literal object Stage 4 analyzes: the theorem of Eisenstat's condensation
paper that characterizes "the same concept". The shared-givens hypothesis is
the place where the roadmap's remark that the observables do some of the work
bites (observables-carry-correspondence); relaxing it is a route of the
improvement claim.

FAF's formalization of the paper carries an errata file and two disclosed
restrictions (universe stratification; the paper's Examples 5.1–5.3 out of
scope), in Formalized Agent Foundations at commit 159ec3f,
Condensation/notes/paper-errata.md, which every comparison with the printed
paper reads first.
