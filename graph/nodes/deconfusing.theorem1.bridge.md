---
id: deconfusing.theorem1.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `deconfusing.theorem1` formalizes the registered claim as the registry reads it: Theorem 1 (three ranges): a violated history scores at most 1 − λ < −δ; a violation-free illegitimate history scores in [−δ, 0); a violation-free legitimate history scores in [0, 1].

## Source
projects/deference/CLAIMS.md, entry `deconfusing.theorem1` (class lean-proved, status active, origin round 2026-10-17-post-companion-formalization; answers item 107).
Documentation: verification: prompts/2026-10-17-post-companion-formalization/REPORT.md; context: prompts/2026-10-17-post-companion-formalization/PROMPT.md; companion: wiki/Deconfusing-Corrigibility-Companion.md.
Short name: Theorem 1 (three ranges): a violated history scores at most 1 − λ < −δ; a violation-free illegitimate history scores in [−δ, 0); a violation-free legitimate history scores in [0, 1].
Conclusion of the signature: `((1 ≤ Sc.N h → Sc.S h ≤ 1 - Sc.lam) ∧ 1 - Sc.lam < -Sc.δ) ∧ (Sc.N h = 0 ∧ ¬ Sc.Legit h → -Sc.δ ≤ Sc.S h ∧ Sc.S h < 0) ∧ (Sc.N h = 0 ∧ Sc.Legit h → 0 ≤ Sc.S h ∧ Sc.S h ≤ 1)`.
