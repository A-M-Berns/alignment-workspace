---
id: computational-updatelessness-direct
kind: or
children: [direct-route-via-b1, direct-route-via-b3, direct-route-via-linked-b2, direct-route-via-luv-coherence]
work:
  - {kind: round, ref: projects/deference/faf-cleanroom-2026-10-02}
tag: either-suffices
author: "@smithy-verity"
size: L
size_reason: "a note section, a paper section and sixteen package reports"
version: 1
---
## Statement
UDT is specified over a logical-induction belief process by treating the
process's future belief states as observations, with a Bayesian logical
inductor supplying coherent probabilities over the large sentences that
describe those states, and the resulting agent satisfies a tiling theorem, by
at least one of four routes: the trajectory prior B1, the measure-valued B3, a
linked B2, or BLI's constraints derived from real-value coherence.

## Source
projects/deference/faf-cleanroom-2026-10-02/sources/references/bli/notion-notes-for-soto-and-diff.md,
section The Research Direction: "The main hope here is to define “observations”
for logical induction in terms of *the future beliefs themselves*. I will call
this the “direct” route to logical updatelessness."

projects/deference/faf-cleanroom-2026-10-02/sources/references/bli/understanding-trust/overleaf-final-source/main.tex,
section What Are Computational Observations?: "These extra rationality
constraints allow us to interpret the non-Bayesian updates of the Logical
Inductor as Bayesian updates again, providing us with a notion of
``observation'' for UDT."

projects/deference/faf-cleanroom-2026-10-02/DIGEST.md, section 3 (the BLI area
of the clean-room run, 2026-09-29 to 10-02); the BLI construction is Sam
Eisenstat's
(projects/deference/faf-cleanroom-2026-10-02/sources/references/bli/README.md).

## Notes
The first mid-level goal of the updateless programme, the maintainer's direct
route of 2023. Filed as an `or` over the four routes the clean-room's BLI
ladder opens (B0 degenerate, B1 the trajectory prior, B2 linked to the market's
quotes, B3 measure-valued) plus the maintainer's 2024 route through LUV
coherence; each route is an `and` of the BLI form in question and the shared
tiling step. The ladder and its decomposition are the clean-room run's, not a
list the sources give. The literal evaluation is of the direct route as stated
with exact constraints; its improvement claim bli-picture-improvable sits
beside it as a shared-claim root of the programme.
