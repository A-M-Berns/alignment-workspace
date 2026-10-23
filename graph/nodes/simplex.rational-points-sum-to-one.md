---
id: simplex.rational-points-sum-to-one
kind: and
children: [simplex.rational-points-sum-to-one.record, simplex.rational-points-sum-to-one.bridge, simplex.rational-points-sum-to-one.complete]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
work:
  - {kind: decision, ref: 2026-08-11--governance-report-removed-relocated}
  - {kind: decision, ref: 2026-08-11--queue-cleared-six-rulings}
author: "@smithy-verity"
---
## Statement
A worked example of the schema, not a research result: the house enumeration checker generates the 28 rational simplex points at denominator six and confirms each sums to one. It exists so the registry, the checker and the CI job are exercised by something real before any research claim depends on them.

## Source
projects/normativity/CLAIMS.md, entry `simplex.rational-points-sum-to-one` (class enumeration-verified, status active, origin round None; answers item 13).
Documentation: verification: checkers/README.md; context: CONTRIBUTING.md.
The checker invocation `enumeration` with parameters {"domain": "rational-simplex", "dimension": 3, "denominator": 6, "property": "satisfies-linear-constraints", "constraints": [{"coefficients": [1, 1, 1], "rhs": 1, "equality": true}]}.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; the hypotheses are the signature's explicit proposition binders, tagged open unless the registry settles them, and the data binders are the setting leaf. Registry note: A worked example of the schema, not a research result: the house enumeration checker generates the 28 rational simplex points at denominator six and confirms each sums to one. It exists so the registry, the checker and the CI job are exercised by something real before any research claim depends on them.
