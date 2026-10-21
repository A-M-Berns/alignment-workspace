---
id: bli-b1-is-logical-inductor
kind: and
children: [bli-b1-is-logical-inductor.record, bli-b1-is-logical-inductor.bridge, tent-oracle-exists, bliov-computable-table, bli-b1-is-logical-inductor.complete]
author: "@smithy-verity"
size: M
size_reason: "one package report and Appendix B of the paper"
version: 1
---
## Statement
B1, the tent trajectory prior over FAF's logical induction algorithm, is a
logical inductor with no open hypothesis.

## Source
projects/deference/faf-cleanroom-2026-10-02/packages/bli-assemble/bli-assemble-report.md:
B1 proved a logical inductor over FAF's LI criterion conditional on the OPEN
statements tentOracle_exists and bliOv_computableTable; the hard step named
there is an output-polynomial FP enumeration of the small sentences that FAF's
machine kits lack.

## Notes
The headline of the clean-room BLI area as a formal result: the composition is
kernel-checked and the two obligations are its open hypothesis leaves, each
carrying the work that would discharge it. The run's digest calls the
enumeration the single step that would turn the area's headline from
conditional to proved.
