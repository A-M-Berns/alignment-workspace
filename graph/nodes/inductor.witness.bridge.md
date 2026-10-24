---
id: inductor.witness.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `inductor.witness` formalizes the registered claim as the registry reads it: the warrant Normative Inductor, run with computability and liability discharged.

## Source
projects/normativity/CLAIMS.md, entry `inductor.witness` (class lean-proved, status active, origin round 2026-10-22-normative-inductor-integration; answers item 35).
Documentation: verification: projects/normativity/rounds/2026-10-22-normative-inductor-integration/THEOREM_STORY.md; context: projects/normativity/rounds/2026-10-22-normative-inductor-integration/HANDOFFS.md.
Short name: the warrant Normative Inductor, run with computability and liability discharged.
Conclusion of the signature: `IsLogicalInductor (W.market DP) DP ∧ (∀ n, Enforced (N n) (res n) → ∀ c ∈ (N n).bundle, excess c.row (W.priceVec DP n) ≤ tol n) ∧ (∀ n, ∀ c ∈ W.bundle n, (∃ o ∈ (N n).survivors, c.cites = Cite.sub o.id ∧ (entitlement n).Entitled o ∧ ∀ j, o.cites = .occurrence j → ∃! o', o' ∈ (N n).survivors ∧ o'.id = j) ∨ (∃ it ∈ (N n).seed.liveStr (N n).docket, c.cites = Cite.str it.id) ∨ ∃ i, c.cites = Cite.settled i) ∧ (∀ s ∈ protocol.services, massOff ((protocol.prob s).gate fun j => W.market DP s (F5.ι j)) (protocol.prob s).A ≤ (protocol.prob s).κ * (protocol.evaluation F5.ι).defect s (W.market DP) ∧ (protocol.evaluation F5.ι).defect s (W.market DP) ≤ (((protocol.prob s).massCap * tol s : ℚ) : ℝ)) ∧ (protocol.evaluation F5.ι).progress (W.market DP) ≤ (protocol.evaluation F5.ι).modulus + (protocol.evaluation F5.ι).error + protocol.D * (protocol.evaluation F5.ι).residual`.
