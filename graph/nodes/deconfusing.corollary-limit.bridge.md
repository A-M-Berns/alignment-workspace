---
id: deconfusing.corollary-limit.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `deconfusing.corollary-limit` formalizes the registered claim as the registry reads it: Corollary (Exploration), the specialization: if ε_K → 0, both conclusions of Theorem 3 hold unchanged.

## Source
projects/deference/CLAIMS.md, entry `deconfusing.corollary-limit` (class lean-proved, status active, origin round 2026-10-17-post-companion-formalization; answers item 107).
Documentation: verification: prompts/2026-10-17-post-companion-formalization/REPORT.md; context: prompts/2026-10-17-post-companion-formalization/PROMPT.md; companion: wiki/Deconfusing-Corrigibility-Companion.md.
Short name: Corollary (Exploration), the specialization: if ε_K → 0, both conclusions of Theorem 3 hold unchanged.
Conclusion of the signature: `LimsupLE (fun K => X.R K - X.T K) 0 ∧ LimsupLE X.R X.τ ∧ ∀ a' : ℕ → A, (∀ k, X.avail k (a' k)) → LimsupLE (X.excess a') 0`.
