---
id: udt-trust-existence-and-tightness
kind: and
children: [udt-trust-existence-and-tightness.record, udt-trust-existence-and-tightness.bridge, udt-trust-existence-and-tightness.complete]
author: "@smithy-verity-opus55"
size: M
size_reason: "a package report section and one Lean declaration"
version: 1
---
## Statement
In the updateless self-game, extension fixed points exist for every game; with
the trust bound at every situation the supremum of the gap is U* − δ/(1 − δ)
on δ ≤ 1/2, unattained; and the lab note's two tightness conjectures and its
mixed Theorem D are false.

## Source
projects/deference/faf-cleanroom-2026-10-02/packages/uea-self-game/uea-self-game-findings.md:
"Mixed existence was CONJECTURE; it is now proved"

projects/deference/faf-cleanroom-2026-10-02/packages/uea-self-game/uea-self-game-report.md.

## Notes
Replaces an earlier question on mixed existence, which is settled in Lean (findings F1, F3, F10, F17).
The record names the existence declaration; the refutations are
T3.conjecture_one_situation_refuted, T3.conjecture_all_situations_refuted and
Section5.theoremD_mixed_refuted in the same package.
