---
id: compiler.schedule-end-to-end.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.EnforcedCompiler.ProjectionSchedule.end_to_end_effective
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: compiler.schedule-end-to-end
---
## Statement
The declaration Workspace.Normativity.Contrib.EnforcedCompiler.ProjectionSchedule.end_to_end_effective is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `compiler.schedule-end-to-end` (class lean-proved, status active, origin round 2026-08-18-projection-enforcement; answers item 48).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-18-projection-enforcement/FINAL_FORMALIZATION_STATUS.md.
The signature of `Workspace.Normativity.Contrib.EnforcedCompiler.ProjectionSchedule.end_to_end_effective` (theorem) in lean/Workspace/Normativity/Contrib/EnforcedCompiler.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (S : ProjectionSchedule)
        {DP : DeductiveProcess} (process : DeductiveProcessComputation DP)
        (hE : EffectiveEnforcerComputation S.enforcer)
        {K : ℕ → (Sentence → ℝ) → Prop} {q : ℕ → Sentence → ℝ}
        (hlocal : ∀ n, FragmentLocal (S.fragment n).toFinset (K n))
        (hKcube : ∀ n y, K n y → ∀ φ ∈ (S.fragment n).toFinset, 0 ≤ y φ ∧ y φ ≤ 1)
        (hq : ∀ n, IsNearestPoint (S.fragment n).toFinset (K n) (S.market DP n) (q n))
        (hrep : ∀ n, ∀ φ ∈ S.coords n,
          repEval (S.fragment n) (S.rep n (DP.D n) φ) (S.market DP n) = q n φ)
        (hadm : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → K n v.payout) :
        IsLogicalInductor (S.market DP) DP ∧
          (∀ n, dist2 (S.fragment n).toFinset (S.market DP n) (q n) ≤ ((S.tol n : ℚ) : ℝ)) ∧
          ∀ n, K n (q n) ∧ ∀ φ ∈ (S.fragment n).toFinset,
            |S.market DP n φ - q n φ| ≤ ((S.tol n : ℚ) : ℝ)
