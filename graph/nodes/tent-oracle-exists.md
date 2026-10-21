---
id: tent-oracle-exists
kind: leaf
leaf_kind: hypothesis
discharge: open
action: "Build the output-polynomial FP enumeration of smallSet n in code order over FAF's machine kits and discharge tentOracle_exists with it."
who: agent
files: [Cleanroom/Bli/BliAssemble/]
work:
  - {kind: open, ref: tentOracle_exists}
author: "@smithy-verity"
size: S
size_reason: "the declaration's hypothesis list"
version: 1
---
## Statement
An oracle exists that enumerates the small sentences of each day in code order
with output-polynomial cost over FAF's machine kits, so that the tent
trajectory prior's table is computable.

## Source
projects/deference/faf-cleanroom-2026-10-02/packages/bli-assemble/bli-assemble-report.md,
the OPEN statement tentOracle_exists and its handoff (stage 5, the FP
enumeration of smallSet n).

## Notes
The hard step of the area; the Lean tasks run through the clean-room's
memory-capped scripts, never bare lake.
