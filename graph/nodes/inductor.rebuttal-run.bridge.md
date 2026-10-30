---
id: inductor.rebuttal-run.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `inductor.rebuttal-run` formalizes the registered claim as the registry reads it: the warrant Normative Inductor, run on the rebuttal of a still-active strength (Scenario B).

## Source
projects/normativity/CLAIMS.md, entry `inductor.rebuttal-run` (class lean-proved, status active, origin round 2026-10-23-normative-inductor-consolidation; answers item 35).
Documentation: verification: projects/normativity/rounds/2026-10-23-normative-inductor-consolidation/THEOREM.md; context: projects/normativity/rounds/2026-10-23-normative-inductor-consolidation/THEOREM_STORY.md.
Short name: the warrant Normative Inductor, run on the rebuttal of a still-active strength (Scenario B).
Conclusion of the signature: `IsLogicalInductor (WB.market DP) DP ∧ (∀ n, Enforced (NB n) (res n) → ∀ c ∈ (NB n).bundle, excess c.row (WB.priceVec DP n) ≤ tol n) ∧ (∀ n, ∀ c ∈ WB.bundle n, (∃ o ∈ (NB n).survivors, c.cites = Cite.sub o.id ∧ (entitlementB n).Entitled o ∧ ∀ j, o.cites = .occurrence j → ∃! o', o' ∈ (NB n).survivors ∧ o'.id = j) ∨ (∃ it ∈ (NB n).seed.liveStr (NB n).docket, c.cites = Cite.str it.id) ∨ ∃ i, c.cites = Cite.settled i) ∧ (∀ s ∈ served.services, massOff ((served.prob s).gate fun j => WB.market DP s (F5.ι j)) (served.prob s).A ≤ (served.prob s).κ * (served.evaluation F5.ι).defect s (WB.market DP) ∧ (served.evaluation F5.ι).defect s (WB.market DP) ≤ (((served.prob s).massCap * tol s : ℚ) : ℝ)) ∧ (served.evaluation F5.ι).progress (WB.market DP) ≤ (served.evaluation F5.ι).modulus + (served.evaluation F5.ι).error + served.D * (served.evaluation F5.ι).residual`.
