---
id: inductor.warrant-inductor.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `inductor.warrant-inductor` formalizes the registered claim as the registry reads it: the warrant Normative Inductor: LI, conformance, provenance, adapter, Progress on one market.

## Source
projects/normativity/CLAIMS.md, entry `inductor.warrant-inductor` (class lean-proved, status active, origin round 2026-10-22-normative-inductor-integration; answers item 35).
Documentation: verification: projects/normativity/rounds/2026-10-22-normative-inductor-integration/THEOREM_STORY.md; context: projects/normativity/rounds/2026-10-22-normative-inductor-integration/HANDOFFS.md.
Short name: the warrant Normative Inductor: LI, conformance, provenance, adapter, Progress on one market.
Conclusion of the signature: `IsLogicalInductor ((schedule N F res tol htol).market DP) DP ∧ (∀ n, Enforced (N n) (res n) → ∀ c ∈ (N n).bundle, excess c.row ((schedule N F res tol htol).priceVec DP n) ≤ tol n) ∧ (∀ n, ∀ c ∈ (schedule N F res tol htol).bundle n, (∃ o ∈ (N n).survivors, c.cites = Cite.sub o.id ∧ (ent n).Entitled o ∧ ∀ j, o.cites = .occurrence j → ∃! o', o' ∈ (N n).survivors ∧ o'.id = j) ∨ (∃ it ∈ (N n).seed.liveStr (N n).docket, c.cites = Cite.str it.id) ∨ ∃ i, c.cites = Cite.settled i) ∧ (∀ s ∈ A.services, massOff ((A.prob s).gate fun j => (schedule N F res tol htol).market DP s (F.ι j)) (A.prob s).A ≤ (A.prob s).κ * (A.evaluation F.ι).defect s ((schedule N F res tol htol).market DP) ∧ (A.evaluation F.ι).defect s ((schedule N F res tol htol).market DP) ≤ (((A.prob s).massCap * tol s : ℚ) : ℝ)) ∧ (A.evaluation F.ι).progress ((schedule N F res tol htol).market DP) ≤ (A.evaluation F.ι).modulus + (A.evaluation F.ι).error + A.D * (A.evaluation F.ι).residual`.
