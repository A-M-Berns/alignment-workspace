---
id: post.witness-learned-weight.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `post.witness-learned-weight` formalizes the registered claim as the registry reads it: Fixed by design against learned: for every day N ≥ 1 a penalty stream with long-run mean 2D has empirical mean 0 ≤ D at day N, so the learned weight leaves the violation undominated there, and dominated past 2N.

## Source
projects/deference/CLAIMS.md, entry `post.witness-learned-weight` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
Short name: Fixed by design against learned: for every day N ≥ 1 a penalty stream with long-run mean 2D has empirical mean 0 ≤ D at day N, so the learned weight leaves the violation undominated there, and dominated past 2N.
Conclusion of the signature: `empiricalWeight (delayedStream D N) N = 0 ∧ score (empiricalWeight (delayedStream D N) N) 0 0 ≤ score (empiricalWeight (delayedStream D N) N) D 1 ∧ ∀ n, 2 * N < n → D < empiricalWeight (delayedStream D N) n ∧ score (empiricalWeight (delayedStream D N) n) D 1 < score (empiricalWeight (delayedStream D N) n) 0 0`.
