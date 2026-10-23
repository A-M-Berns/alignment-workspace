---
id: shortfall.deferred-ahead.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `shortfall.deferred-ahead` formalizes the registered claim as the registry reads it: The shortfall atom is priced ahead of deduction: decided by the process only at its deferred stage, its day-n price tends to one along a family the process eventually proves short.

## Source
projects/deference/CLAIMS.md, entry `shortfall.deferred-ahead` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/FOLLOWUP.md.
Short name: The shortfall atom is priced ahead of deduction: decided by the process only at its deferred stage, its day-n price tends to one along a family the process eventually proves short.
Conclusion of the signature: `(∀ n, shortAtom (a n) ∉ (shortfallProcess short defer).D n) ∧ ∃ N, ∀ n, N ≤ n → θ ≤ P n (shortAtom (a n))`.
