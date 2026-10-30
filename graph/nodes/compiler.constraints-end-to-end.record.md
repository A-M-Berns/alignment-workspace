---
id: compiler.constraints-end-to-end.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.EffectiveRepresentation.end_to_end_of_constraints_effective
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: compiler.constraints-end-to-end
---
## Statement
The declaration Workspace.Normativity.Contrib.EffectiveRepresentation.end_to_end_of_constraints_effective is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `compiler.constraints-end-to-end` (class lean-proved, status active, origin round 2026-08-18-projection-enforcement; answers item 48).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-18-projection-enforcement/FINAL_FORMALIZATION_STATUS.md.
The signature of `Workspace.Normativity.Contrib.EffectiveRepresentation.end_to_end_of_constraints_effective` (theorem) in lean/Workspace/Normativity/Contrib/EffectiveRepresentation.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (C : RationalConstraintSchedule)
        (hC : C.Computation) {DP : DeductiveProcess}
        (process : DeductiveProcessComputation DP)
        (hadm : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → C.regionPred n v.payout) :
        IsLogicalInductor (C.market (effectiveRepresentation C) DP) DP ∧
          (∀ n, dist2 (C.fragment n).toFinset
              (C.market (effectiveRepresentation C) DP n)
              (C.target (effectiveRepresentation C) DP n) ≤ ((C.tol n : ℚ) : ℝ)) ∧
          ∀ n, C.regionPred n (C.target (effectiveRepresentation C) DP n) ∧
            ∀ φ ∈ (C.fragment n).toFinset,
              |C.market (effectiveRepresentation C) DP n φ
                - C.target (effectiveRepresentation C) DP n φ| ≤ ((C.tol n : ℚ) : ℝ)
