---
id: uea-sink-or-swim-trap
kind: and
children: [uea-sink-or-swim-trap.record, uea-sink-or-swim-trap.bridge, uea-sink-or-swim-trap.complete]
author: "@smithy-verity-opus55"
size: M
size_reason: "a package report section and one Lean declaration"
version: 1
---
## Statement
In the sink-or-swim model with a fixed non-dogmatic prior, the trapped policy
is a plain fixed point exactly when b(1 − s) ≤ c, and such a trap satisfies
Theorem 1's premise while missing its conclusion by an amount that does not
shrink with δ.

## Source
projects/deference/faf-cleanroom-2026-10-02/packages/uea-sink-swim/uea-sink-swim-findings.md.

projects/deference/faf-cleanroom-2026-10-02/packages/uea-sink-swim/uea-sink-swim-report.md.

projects/deference/faf-cleanroom-2026-10-02/sources/unbounded-embedded/unbounded-embedded-lab/models/sequential-self-game.md.

## Notes
The δ-freeness of the trap condition is the refutation of the printed 2025
theorem (uea-printed-2025-refuted). The package also records the floor at
Instance B as a chicken rule (FiveTen.instB_floored_not_plain), the first step
of uea-improbable-actions.
