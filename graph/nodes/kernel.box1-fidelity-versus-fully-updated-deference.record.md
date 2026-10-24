---
id: kernel.box1-fidelity-versus-fully-updated-deference.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Headline.box1_one_model
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: kernel.box1-fidelity-versus-fully-updated-deference
---
## Statement
The declaration Workspace.Deference.Headline.box1_one_model is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `kernel.box1-fidelity-versus-fully-updated-deference` (class lean-proved, status active, origin round 2026-09-27-corrigibility-kernel-phase2; answers item 104).
Documentation: verification: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md; context: prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md.
The signature of `Workspace.Deference.Headline.box1_one_model` (theorem) in lean/Workspace/Deference/Spec/Headline.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {Q : Type*} (P : LexParams) (v b : Q → ℝ) (ask act : Q) (r : ℝ)
        (hcal : ∀ x, |v x - b x| ≤ r) (hagree : v ask = v act) (hb : b act ≤ P.D)
        (pS pT : ℝ) (hp : 0 ≤ pS + pT) (qp qm vp vm : ℝ) (resp : Bool)
        (hqp : |qp - vp| ≤ r) (hqm : |qm - vm| ≤ r) :
        b ask - b act ≤ 2 * r ∧
          P.ϖ - (P.D - b ask) ≤ P.evalOf (b ask) 0 0 0 - P.evalOf (b act) 1 pS pT ∧
          |Workspace.Deference.Contrib.ProtectedAuthority.outcomeRes2 qp qm vp vm resp| ≤ 2 * r
