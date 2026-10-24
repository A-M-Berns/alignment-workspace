---
id: thin.reflection-inherited-value.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `thin.reflection-inherited-value` formalizes the registered claim as the registry reads it: Reflection is the trivial baseline: a correct credence satisfies the inherited Value through total trust.

## Source
projects/deference/CLAIMS.md, entry `thin.reflection-inherited-value` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
Short name: Reflection is the trivial baseline: a correct credence satisfies the inherited Value through total trust.
Conclusion of the signature: `∀ (X : W → ℝ) (s : ℝ), s * (∑ w, π w) ≤ ∑ w, π w * (if s ≤ (∑ v, credenceOf a V w v * X v) then X w else s)`.
