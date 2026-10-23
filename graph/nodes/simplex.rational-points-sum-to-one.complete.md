---
id: simplex.rational-points-sum-to-one.complete
kind: leaf
leaf_kind: completeness
size: S
size_reason: "one signature against its binders"
version: 1
author: "@smithy-verity"
---
## Statement
No premise beyond the signature's binders enters the declaration; the kernel checks it as stated.

## Source
The checker invocation `enumeration` with parameters {"domain": "rational-simplex", "dimension": 3, "denominator": 6, "property": "satisfies-linear-constraints", "constraints": [{"coefficients": [1, 1, 1], "rhs": 1, "equality": true}]}.
