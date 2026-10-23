---
id: post.theorem.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `post.theorem` formalizes the registered claim as the registry reads it: The post's theorem: three hypotheses, two conclusions.

## Source
projects/deference/CLAIMS.md, entry `post.theorem` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
Short name: The post's theorem: three hypotheses, two conclusions.
Conclusion of the signature: `((∀ a, H.Viol a = true → H.eval a < H.eval H.queue) ∧ (∀ a, H.eval H.queue ≤ H.eval a → H.nKnown a = 0 ∧ H.p a ≤ (H.P.D - H.c) / H.P.ϖ)) ∧ (∀ {X : Type} [Fintype X] (μ : X → ℝ), (∀ x, 0 ≤ μ x) → ∀ (ordT ordπ nπ : X → ℝ) (viol : X → Bool), (∀ x, viol x = false → ordT x = ordπ x ∧ nπ x = 0) → (∀ x, viol x = true → 1 ≤ nπ x ∧ H.P.w ≤ ordT x ∧ ordπ x ≤ H.P.D) → expectR μ (fun x => score H.P.ϖ (ordT x) 0) - expectR μ (fun x => score H.P.ϖ (ordπ x) (nπ x)) ≥ (H.P.ϖ - (H.P.D - H.P.w)) * expectR μ (fun x => indR (viol x)))`.
