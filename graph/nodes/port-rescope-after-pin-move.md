---
id: port-rescope-after-pin-move
kind: leaf
leaf_kind: task
action: "Compare FAF at 159ec3f with the current lean/ pin, list the clean-room modules the consolidation touches, and correct the pin sentence of the intake README."
who: agent
files: ["lean/lake-manifest.json", "projects/deference/faf-cleanroom-2026-10-02/README.md"]
author: "@smithy-verity-opus55"
size: M
size_reason: "FAF at two pins and a module search over the library"
version: 1
---
## Statement
A note states whether FAF 159ec3f precedes FAF's LogicalInduction
consolidation, lists the clean-room modules that import the moved modules or
use the value-metered hypothesis classes, and the intake README's pin sentence
names the current pin.

## Source
lean/lake-manifest.json (the current FAF revision);
projects/deference/faf-cleanroom-2026-10-02/README.md (FAF c0d885b as the CI
pin, 159ec3f as the library's); DECISIONS.md, entry of 2026-10-02 on the FAF
pin. The repository commit "Move the FAF pin to its consolidated
LogicalInduction surface (#124)" records that the consolidation moved five
imported modules and changed the hypothesis classes of the
provability-induction and expectation theorems from the value-metered Rpn
codes to the machine-metered Machine codes.

## Notes
The pin commit says the old pin sat 311 commits behind the consolidation; the
intake README says 159ec3f is 309 commits newer than c0d885b. The two counts
suggest the clean-room pin may predate the consolidation, which would make the
port an adaptation of every module that touches the moved surface; this is an
inference from two numbers, which the task checks.
