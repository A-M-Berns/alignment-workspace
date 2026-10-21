---
id: li-shutdown-decided-weight
kind: leaf
leaf_kind: step
action: "Lift the probe decidedWeight_factors into corr-li-shutdown, delete the open statement, and rewrite finding F19 as the positive result."
who: agent
files: [projects/deference/faf-cleanroom-2026-10-02/packages/corr-li-shutdown]
work:
  - {kind: open, ref: decidedWeight_factors_open}
author: "@smithy-verity"
size: M
size_reason: one probe and one open statement
version: 1
---
## Statement
Item 4 of the logical-induction wiki's open problems, in product form at the
library's mesh, follows from expectation provability induction with a feature
coefficient, by a proof that exists as an audit probe of about one hundred and
ten lines and is not in the library.

## Source
projects/deference/faf-cleanroom-2026-10-02/DIGEST.md, section 6, item 6 (the
round-4 probe proves decidedWeight_factors_open, about 110 lines; a research
result, the wiki's open-problems item 4 in product form);
projects/deference/faf-cleanroom-2026-10-02/packages/corr-li-shutdown, the open
statement decidedWeight_factors_open (statement T2(b), reading (a)).

## Notes
A proof that exists in a probe while the library still carries the open
statement; lifting it is the action.
