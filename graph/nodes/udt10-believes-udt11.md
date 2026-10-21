---
id: udt10-believes-udt11
kind: cases
children: [udt10-believes-udt11.partition, pic-udt-pointwise-reading, pic-udt-self-consistent-reading, pic-udt-margin-reading, pic-udt-residual-reading]
rows:
  - {picture: pic-udt-pointwise-reading, class: null, observable: never, given: udt-trust-pointwise-refuted@valid}
  - {picture: pic-udt-self-consistent-reading, class: null, observable: never, given: udt-trust-repaired@valid}
  - {picture: pic-udt-margin-reading, class: null, observable: never, given: udt-trust-margin-reading@valid}
  - {picture: pic-udt-residual-reading, class: undescribed-failure, observable: never, residual: true}
author: "@smithy-verity-opus55"
size: M
size_reason: "one sentence of the review against three formal readings"
version: 1
---
## Statement
If a UDT1.0 agent assigns probability at least 1 − δ to its policy being
UDT1.1, then it is ε-optimal.

## Source
projects/deference/faf-cleanroom-2026-10-02/sources/unbounded-embedded/01-primary/summer-research-plan-2026--research-ideas-may-2026.md:
"I'm imagining a theorem something like: if a UDT1.0 agent
$(1-\delta)$-believes that its policy is UDT1.1, then it is
$\varepsilon$-optimal."

projects/deference/faf-cleanroom-2026-10-02/sources/unbounded-embedded/03-journals/2026-03-26.md:
"it believes the _chosen_ policy = udt 1.1, not the _enacted_ policy"

projects/deference/faf-cleanroom-2026-10-02/packages/uea-self-game/uea-self-game-findings.md.

## Notes
The research plan's proposed theorem (May 2026), filed as a table over the
readings of 'believes its policy is UDT1.1' that the finite updateless
self-game formalized: the pointwise static-belief reading (refuted), the
self-consistency reading (proved with a δ/(1 − δ) bound) and the margin
reading (proved beyond a margin, total loss at near ties). Each row conditions
on the formal result for its reading. Which reading the proposal intends is
ATTRIBUTION-UNVETTED in the package's own words (finding F11). The
updateless-dt branch links to this node;
it lives in Cole Wyeth's unbounded setting. The table is proposed until a
human admits its rows.
