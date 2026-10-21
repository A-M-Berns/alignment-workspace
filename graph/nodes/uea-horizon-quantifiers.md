---
id: uea-horizon-quantifiers
kind: and
children: [uea-horizon-quantifiers.record, uea-horizon-quantifiers.bridge, uea-horizon-quantifiers.complete]
author: "@smithy-verity-opus55"
size: M
size_reason: "a package report section and one Lean declaration"
version: 1
---
## Statement
In the finite shadow, for every ε and horizon T there is a δ that makes the
self-trusting agent ε-optimal, but without discounting (γ = 1) no single δ
serves every horizon.

## Source
projects/deference/faf-cleanroom-2026-10-02/DIGEST.md: "`∀ε ∀T ∃δ` holds and
`∀ε ∃δ ∀T` fails"

projects/deference/faf-cleanroom-2026-10-02/packages/uea-sink-swim/uea-sink-swim-report.md.

## Notes
A constraint on uea-rosi-lift (AI reading): a horizon-free δ in rOSI needs
discounting or another ingredient. The live post assumes summable discounts,
so this result bears on the undiscounted reading only.
