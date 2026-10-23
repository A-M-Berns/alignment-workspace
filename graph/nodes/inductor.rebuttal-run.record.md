---
id: inductor.rebuttal-run.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.WarrantInductorRebuttal.inductor
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: inductor.rebuttal-run
---
## Statement
The declaration Workspace.Normativity.Contrib.WarrantInductorRebuttal.inductor is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `inductor.rebuttal-run` (class lean-proved, status active, origin round 2026-10-23-normative-inductor-consolidation; answers item 35).
Documentation: verification: projects/normativity/rounds/2026-10-23-normative-inductor-consolidation/THEOREM.md; context: projects/normativity/rounds/2026-10-23-normative-inductor-consolidation/THEOREM_STORY.md.
The signature of `Workspace.Normativity.Contrib.WarrantInductorRebuttal.inductor` (theorem) in lean/Workspace/Normativity/Contrib/WarrantInductorRebuttal.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    :
        IsLogicalInductor (WB.market DP) DP ∧
        (∀ n, Enforced (NB n) (res n) →
          ∀ c ∈ (NB n).bundle, excess c.row (WB.priceVec DP n) ≤ tol n) ∧
        (∀ n, ∀ c ∈ WB.bundle n,
          (∃ o ∈ (NB n).survivors, c.cites = Cite.sub o.id ∧ (entitlementB n).Entitled o ∧
            ∀ j, o.cites = .occurrence j → ∃! o', o' ∈ (NB n).survivors ∧ o'.id = j) ∨
          (∃ it ∈ (NB n).seed.liveStr (NB n).docket, c.cites = Cite.str it.id) ∨
          ∃ i, c.cites = Cite.settled i) ∧
        (∀ s ∈ served.services,
          massOff ((served.prob s).gate fun j => WB.market DP s (F5.ι j)) (served.prob s).A ≤
            (served.prob s).κ * (served.evaluation F5.ι).defect s (WB.market DP) ∧
          (served.evaluation F5.ι).defect s (WB.market DP) ≤
            (((served.prob s).massCap * tol s : ℚ) : ℝ)) ∧
        (served.evaluation F5.ι).progress (WB.market DP) ≤
          (served.evaluation F5.ι).modulus + (served.evaluation F5.ι).error +
            served.D * (served.evaluation F5.ι).residual
