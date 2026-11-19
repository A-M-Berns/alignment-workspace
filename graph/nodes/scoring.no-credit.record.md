---
id: scoring.no-credit.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.ScoringTheorem.Audit.no_credit
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@claude-fable-5-2"
registry_id: scoring.no-credit
---
## Statement
The declaration Workspace.Deference.Contrib.ScoringTheorem.Audit.no_credit is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `scoring.no-credit` (class lean-proved, status active, origin round 2026-11-10-legitimacy-definition-prosecution; answers item 137).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/SCORING.md; context: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN.md.
The signature of `Workspace.Deference.Contrib.ScoringTheorem.Audit.no_credit` (theorem) in lean/Workspace/Deference/Contrib/ScoringTheorem.lean, verbatim, binders included, after the section variables in scope (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    variable {X : Type*} (A : Audit X)
    variable [Fintype X]

    (ν : X × Bool × Bool → ℝ) (κ : ℝ) (hα : 0 ≤ A.α) (hδ : 0 ≤ A.δ)
        (hδκ : 1 ≤ A.δ * κ) (hv : ∀ x, A.v x ≤ 1) (hν : ∀ y, 0 ≤ ν y) (h4 : A.Indep ν)
        (h3d : A.D3det (marg ν) κ) :
        expectR ν A.score
          ≤ A.α * expectR (marg ν) (fun x => A.v x * ind (!A.C x))
            - A.lam * expectR (marg ν) (fun x => (A.N x : ℝ))
