---
id: compiler.deductive-end-to-end.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.DeductiveEffective.deductive_end_to_end
hypotheses: [compiler.deductive-end-to-end.h-fragment-schedule, compiler.deductive-end-to-end.h-tolerance-schedule, compiler.deductive-end-to-end.h-process-certificate, compiler.deductive-end-to-end.h-stages-satisfiable]
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: compiler.deductive-end-to-end
---
## Statement
The declaration Workspace.Normativity.Contrib.DeductiveEffective.deductive_end_to_end is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `compiler.deductive-end-to-end` (class lean-proved, status active, origin round 2026-08-18-projection-enforcement; answers item 48).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-18-projection-enforcement/FINAL_FORMALIZATION_STATUS.md.
The signature of `Workspace.Normativity.Contrib.DeductiveEffective.deductive_end_to_end` (theorem) in lean/Workspace/Normativity/Contrib/DeductiveEffective.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (coords : ℕ → List Sentence)
        (nodup : ∀ n, (coords n).Nodup) (tol : ℕ → ℚ) (tol_pos : ∀ n, 0 < tol n)
        (hcoords : Primrec coords) (htol : Primrec tol)
        {DP : DeductiveProcess} (process : DeductiveProcessComputation DP)
        (hsat : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
        IsLogicalInductor
            ((deductiveProjectionSchedule coords nodup tol tol_pos).market DP) DP ∧
          ∀ n, dist2 ((deductiveProjectionSchedule coords nodup tol tol_pos).fragment n).toFinset
              ((deductiveProjectionSchedule coords nodup tol tol_pos).market DP n)
              (fun φ => ProjectionCompiler.repEval
                ((deductiveProjectionSchedule coords nodup tol tol_pos).fragment n)
                ((deductiveProjectionSchedule coords nodup tol tol_pos).rep n (DP.D n) φ)
                ((deductiveProjectionSchedule coords nodup tol tol_pos).market DP n))
            ≤ ((tol n : ℚ) : ℝ)
## Notes
Filed by the map-as-canonical round from the registry entry and the declaration's signature; its hypotheses were unread (ruling F1, 2026-10-23) until the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice) filed the four hypothesis leaves by reading the declaration and the file's header: the fragment schedule, the tolerance schedule, the source's computability certificate on the process, and the satisfiability of every stage. The signature stays in the Source as the text they were read from.
