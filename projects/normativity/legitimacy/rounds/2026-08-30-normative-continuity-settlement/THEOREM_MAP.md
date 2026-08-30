# What is claimed, and on what

Delta over `../2026-08-29-normative-continuity-concordance/THEOREM_MAP.md`, whose
entries 1–5, the Step lemmas, and fixtures F1–F7 stand unchanged (the spine's proofs
were not touched; the file grew by §4). Every Lean name below audits to
`[propext, Classical.choice, Quot.sound]` (28 `#print axioms` lines, all clean, build log
in `REPORT.md`). Nothing is registered.

## Settlement additions

| # | claim | class | check |
|---|---|---|---|
| S1 | The paper's matter construction realizes the abstract fields: `mattersOf` is monotone and every matter is a prior issue, given only `Desig_n ⊆ O_n ∪ Q⁺_n` | LEAN-VERIFIED | `IssueTraceCore.mattersOf_mono`, `mattersOf_prior`, realization `IssueTraceCore.toIssueTrace` |
| S2 | Matterhood is prospective and never retroactive | LEAN-VERIFIED | `mem_mattersOf_succ`, `mattersOf_not_mem_of_lt` |
| S3 | Merge and split: a joint successor is live for every parent's matter; each successor of a live descendant is live | LEAN-VERIFIED | `anc_of_parent`, `mem_live_succ_of_parent` |
| S4 | **Grounded Replay, historical form**: every admitted occurrence (`Adm_n = G ∪ ⋃_{j<n} L_j^+`) has an authorization tree; the live form is a corollary | LEAN-VERIFIED from Requirement 1 | `StandingTrace.grounded_replay_admitted`, `grounded_replay_live`, `L_subset_Adm` |
| S5 | Wait responsiveness: the primitive "no permanent no-route wait" form and the "eventually `Met`" form are equivalent; Persistent Opportunity from the primitive | LEAN-VERIFIED | `IssueTrace.NoPermanentWait`, `noPermanentWait_of_waitResponsive`, `waitResponsive_of_noPermanentWait`, `persistent_opportunity'` |
| S6 | Positive-share attention: for any injective index, `0 ≤ a ≤ 1[opp]`, `Σ_{m∈S} a_n(m) ≤ 1` for every finite `S`, `A_N(m) = w_m Ω_N(m)`, hence non-starvation for every matter | LEAN-VERIFIED | `shareAttention_nonneg`, `shareAttention_le_opp`, `shareAttention_sum_le_one`, `attention_share_eq`, `shareAttention_nonStarving` |
| S7 | The issue-trace specification is inhabited (fixture E satisfies every requirement including the reach gate) | LEAN-VERIFIED | `Fixtures.fixE_other_requirements`, `fixE_reach_gate`, `fixE_issueTrace`, `fixE_issueTrace_nonvacuous` |
| S8 | The *whole* settled specification (standing, Due, anchors, issues, attention, gate) is jointly satisfiable by a nontrivial trace exercising every departure and the red-team shapes | FINITE-TEST-SUPPORTED | `src/settled_model.py` witness `W`; `tests/test_settled.py` |
| S9 | Under the settled choices, same-batch open-and-resolve and preexisting successors are refused, and consolidation by a route edge credits the matter | FINITE-TEST-SUPPORTED | `TestSettledChoicesRegressions` |

## Dependency report after settlement

Unchanged from the concordance round: Persistent-Wait consumes `IssueTrace`'s fields for
Requirements 4, 5, 7, 8, 9, 10, 12 and the bookkeeping fields; Persistent Opportunity
adds `WaitResponsive` (or, equivalently, `NoPermanentWait`); No Structural Abandonment
adds `NonStarving`; Grounded Replay (both forms) uses `StandingTrace`'s three fields
and not `Fresh`. The realization `toIssueTrace` shows the two bookkeeping fields about
`M` are exactly what the paper's construction supplies — no additional property was
needed. `born_not_out` remains a stated field no proof uses.

## What no entry above claims

That wait responsiveness or non-starvation hold of anything (S6 shows non-starvation is
*satisfiable*, not that any given process satisfies it). That the eight judgments have a
realization. Anything about Coverage, Progress, Proper Exercise, checkers, or liability.
