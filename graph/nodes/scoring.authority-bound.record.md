---
id: scoring.authority-bound.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.ScoringTheorem.Audit.authority_bound
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@claude-fable-5-2"
registry_id: scoring.authority-bound
---
## Statement
The declaration Workspace.Deference.Contrib.ScoringTheorem.Audit.authority_bound is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `scoring.authority-bound` (class lean-proved, status active, origin round 2026-11-10-legitimacy-definition-prosecution; answers item 137).
Documentation: verification: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/SCORING.md; context: projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/account/LEAN.md.
The signature of `Workspace.Deference.Contrib.ScoringTheorem.Audit.authority_bound` (theorem) in lean/Workspace/Deference/Contrib/ScoringTheorem.lean, verbatim, binders included, after the section variables in scope (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    variable {X : Type*} (A : Audit X)
    variable [Fintype X]

    {P : Type*} (ν : P → X × Bool × Bool → ℝ) (p p' : P)
        (εd ηd φ γ : ℝ) (hα : 0 < A.α) (hδ : 0 ≤ A.δ) (hlam : 0 < A.lam) (hφ : 0 ≤ φ)
        (hv : ∀ x, A.v x ≤ 1)
        (hν : ∀ y, 0 ≤ ν p y) (hs : ∑ y, ν p y = 1)
        (hν' : ∀ y, 0 ≤ ν p' y) (hs' : ∑ y, ν p' y = 1)
        (h4 : A.Indep (ν p)) (h4' : A.Indep (ν p'))
        (h1b : A.D1b (marg (ν p')) εd) (h2b : A.D2b (marg (ν p')) ηd)
        (h3 : A.D3fp (marg (ν p')) φ) (h5 : A.D5 (marg (ν p'))) (h6 : A.D6 ν p γ) :
        expectR (marg (ν p)) (fun x => (A.N x : ℝ))
          ≤ A.α * (1 - expectR (marg (ν p')) A.fbar + (εd + ηd + A.δ * φ + γ / A.α))
            / A.lam
