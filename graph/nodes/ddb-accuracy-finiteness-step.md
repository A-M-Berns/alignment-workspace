---
id: ddb-accuracy-finiteness-step
kind: leaf
leaf_kind: question
action: "Identify which step of totalTrustOn_iff_epistemicValueOn uses finiteness of the frame, and say whether a countable version needs a different scoring-rule class."
who: agent
files: [projects/deference/faf-cleanroom-2026-10-02/Cleanroom/Lit/LitDdbAccuracyMm/Accuracy.lean]
author: "@smithy-verity-opus55"
size: M
size_reason: "one Lean proof to read for its use of Fintype"
version: 1
---
## Statement
Exactly one step of the kernel-checked finite proof of Deference Done Better's
accuracy theorem uses finiteness of the frame, and it can be named.

## Source
projects/deference/faf-cleanroom-2026-10-02/packages/lit-ddb-accuracy-mm/lit-ddb-accuracy-mm-report.md.

projects/deference/faf-cleanroom-2026-10-02/Cleanroom/Lit/LitDdbAccuracyMm/Accuracy.lean.

## Notes
Replaces the first half of an earlier task on porting the accuracy proof,
whose premise was false: Theorem 3.2 is proved both ways
(totalTrustOn_iff_epistemicValueOn). Bears on
frames-beyond-finite and on the li-trust branch's accuracy translation.
