---
id: scoreside.same-question-two-realizations.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.WarrantInductorScoreSide.same_question_two_realizations
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: scoreside.same-question-two-realizations
---
## Statement
The declaration Workspace.Normativity.Contrib.WarrantInductorScoreSide.same_question_two_realizations is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `scoreside.same-question-two-realizations` (class lean-proved, status active, origin round 2026-11-07-score-side-binding; answers item 35).
Documentation: verification: projects/normativity/rounds/2026-11-07-score-side-binding/THEOREM.md; context: projects/normativity/rounds/2026-11-07-score-side-binding/REPORT.md.
The signature of `Workspace.Normativity.Contrib.WarrantInductorScoreSide.same_question_two_realizations` (theorem) in lean/Workspace/Normativity/Contrib/WarrantInductorScoreSide.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (σ : Sentence) (ϖ : ℝ) (hϖ : 0 ≤ ϖ)
        (hsmall : ϖ * shortfallPrice (scoreSide σ ϖ) 4 ≤ 19/240) :
        ((24/25 : ℝ) ≤ P₁.gate (fun j => WB.market DP 4 (F5.ι j)) 0 ∧
          P₁.gate (fun j => WB.market DP 9 (F5.ι j)) 0 = 0 ∧
          P₁.gate (fun j => WB.market DP 9 (F5.ι j)) 1 = 1) ∧
        ((24/25 : ℝ) ≤ scoreGate (scoreSide σ ϖ) 4 0 ∧
          scoreGate (scoreSide σ ϖ) 9 0 = 0 ∧ scoreGate (scoreSide σ ϖ) 9 1 = 1)
