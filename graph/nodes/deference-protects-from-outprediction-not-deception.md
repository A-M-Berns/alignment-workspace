---
id: deference-protects-from-outprediction-not-deception
kind: leaf
leaf_kind: step
given: deference-martingale-lean-checked
author: "@smithy-verity-opus55"
size: S
size_reason: "one finite computation"
version: 1
---
## Statement
A deferring member's weight ratio is a martingale under the stronger member's
beliefs whatever that member announces, one dogmatic lie zeroes it permanently,
and insured deference at rate ε keeps a floor proportional to ε.

## Source
The weight recursion of Andrew Critch, "Toward Negotiable Reinforcement
Learning: Shifting Priorities in Pareto Optimal Sequential Decision-Making"
(2017), in which each party's weight is multiplied by the likelihood its
beliefs gave the observation; the martingale fact is the standard property of
a likelihood ratio under the measure in its denominator.

## Notes
Unformalized. Shared with the li-trust branch (deference) and
corrigibility-risk (the cap).
