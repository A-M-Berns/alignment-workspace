---
id: decision-problems-lean-done
kind: and
children: [decision-problems-lean-done.record, decision-problems-lean-done.bridge, finite-tree-semantics-setting, decision-problems-lean-done.complete]
author: "@smithy-verity"
size: L
size_reason: "seventeen package reports and a draft"
version: 1
---
## Statement
On strongly fair finite trees every strict local maximum of the formal core's
optimality notion is global (Theorems 1 and 2 of the formal core transposed to
trees), kernel-checked; the remaining load-bearing propositions of sections 3
to 8 and the fairness and relocation repair are checked in the other dp
packages, or refuted with their surviving neighbours stated.

## Source
projects/deference/faf-cleanroom-2026-10-02/packages/dp-local-opt/dp-local-opt-report.md:
stronglyFair_strictLocalMax_isOptimal, almostFair_strictLocalMax_not_isOptimal.
The sixteen dp-* packages under
projects/deference/faf-cleanroom-2026-10-02/packages/ (dp-core-tree,
dp-calibration, dp-calib-limits, dp-fairness-reloc, dp-edt-udt-fair,
dp-faithful-udt, dp-smoking-lesion, dp-two-lesions, dp-worlds-jb,
dp-devices-catalog, dp-dutch-book, dp-firstperson-sc, dp-cartesian-frames,
dp-referents-cdt, dp-causal-consist, dp-learner-nr, dp-troll-bridge);
projects/deference/faf-cleanroom-2026-10-02/DIGEST.md, the decision areas.

## Notes
The local-optimum theorem (stronglyFair_strictLocalMax_isOptimal) is the
record;
the parent names the packages that check the rest. Fourteen of seventeen
decision packages passed; the probe witnesses of dp-calib-limits and
dp-fairness-reloc await a lift (listed in the branch's notes).
