---
id: third-button-obstruction
kind: leaf
leaf_kind: assumption
author: "@smithy-verity"
size: S
size_reason: "two lines of the working notes and one declaration"
version: 1
---
## Statement
When every instance of an agent trusts the others to follow a shared plan, some
instance can be a defector who spoils the plan even though all instances share
goals and beliefs, so message-based self-modification needs a stability
assumption beyond shared goals.

## Source
projects/deference/faf-cleanroom-2026-10-02/sources/references/bli/understanding-trust/udt-tiling-working-notes-2025-06-30.md,
line 1130 (the maintainer): "However, the Third Button problem discussed in
Section 3 shows that this doesn't always work. In some cases, everyone trusting
others to follow the plan leads to ``defectors'' who spoil the plan, even in
cases where everyone shares the same goals and beliefs!" and line 1132:
"Clearly, we need some additional assumptions to rule out such
counterexamples."

projects/deference/faf-cleanroom-2026-10-02/packages/udt-paper-tiling/udt-paper-tiling-report.md:
CommClone.naive_cloning_refuted, the Lean form.

## Notes
Stated by the maintainer in 2025; the clean-room's refutation of
single-instance communicative cloning is its Lean form, a result he had already
drawn in prose.
