# What is claimed, and on what

Classes are `AGENTS.md`'s. Nothing here is registered. Lean names live in
`lean/Workspace/Normativity/Contrib/NormativeContinuity.lean`; every listed Lean result
audits to `[propext, Classical.choice, Quot.sound]` (build log in `REPORT.md`).

## The theorem spine

| # | claim | class | check |
|---|---|---|---|
| 1 | **Persistent-Wait.** A matter that exists from `n₀`, is live at every `n ≥ n₀`, and has bounded `Ω_N(m)` has a fixed prerequisite `d` and `N₀` with `d ∈ NoRoute_n(m)` for all `n ≥ N₀` | LEAN-VERIFIED under the `IssueTrace` hypotheses | `IssueTrace.persistent_wait` |
| 2 | **Persistent Opportunity.** Add wait responsiveness: a matter live forever has `Ω_N(m)` unbounded | LEAN-VERIFIED, parametric in `WaitResponsive` | `IssueTrace.persistent_opportunity` |
| 3 | **No Structural Abandonment.** Add non-starvation for an attention function `a`: eventually `Live_n(m) = ∅`, or `A_N(m)` unbounded | LEAN-VERIFIED, parametric in `WaitResponsive` and `NonStarving`; the unit-budget constraints on `a` are not hypotheses | `IssueTrace.no_structural_abandonment` |
| 4 | **Grounded Replay.** Every `λ ∈ L_n` has a finite authorization tree with leaves in `G` and positions strictly decreasing along branches | LEAN-VERIFIED from Requirement 1 | `StandingTrace.grounded_replay`; the tree is the inductive `Grounded` |
| 5 | Standing-at-opening connects the layers: the rule licensing a fresh issue's protocol is grounded | LEAN-VERIFIED | `anchor_grounded` |

## Load-bearing lemmas (the paper proof's steps)

| paper step | Lean | uses |
|---|---|---|
| Lemma 6, reachable resolution is work | `mem_work_of_res` | Req 10 |
| Step 1 | `not_res_of_reach` | Lemma 6 |
| Step 2, live lineage frozen | `live_succ_eq` | Req 4, 5, `matters_prior` |
| Step 2, no prerequisite added | `pre_succ_subset` | Req 7, **12** |
| Step 2, route sets frozen | `routes_succ_eq` | Req 4, 5, **8** (`root_born_lt`) |
| Step 2, reach shrinks | `reach_succ_subset` | the three above, Req **9** |
| Step 3, stabilization | `nat_antitone_stabilizes`, `finset_antitone_stabilizes` | finiteness |
| Step 4, sink | `exists_sink` | `Finite.wellFounded_of_trans_of_irrefl` |
| Step 5, wait persists | stabilization of the unmet-pair set, `routes_empty_persistent` | Req 8 |
| Lemma 3 (repaired), route loss permanent after introduction | `routes_empty_persistent` | Req 4, 5, 8 |
| Lemma 2, matter continuity | `live_empty_persistent` | Req 4, 5, `matters_prior` |
| bounded `Ω` ⇒ eventually no work | `eventually_no_opp` | — |

## Dependency report: Lean against the proof-pass table

| result | proof pass said | Lean hypotheses (fields of the structure consumed) | agreement |
|---|---|---|---|
| Persistent-Wait | Req 4, 5, 7, 8, 9, 10, 12 + finite batches | `IssueTrace`: `resolution_continuity` (4), `fresh_successors` (5), `pre_continuity`/`pre_fresh`/`pre_intro` (7), `pre_refs` (8), `met_persistent` (9), `ready_resolve` (10), `no_rewire` (12); bookkeeping `born_unique`, `born_not_out`, `out_born`, `res_subset`, `matters_mono`, `matters_prior`; finiteness by `Finset` | exact. The bookkeeping fields are the paper's "positions form a list" and "matters are prior issues", which the paper uses without naming; `born_not_out` is stated but not consumed by any proof |
| Persistent Opportunity | + wait responsiveness | + `WaitResponsive` | exact |
| No Structural Abandonment | + Req 11 | + `NonStarving`; budget constraints absent | exact; the paper's `0 ≤ a ≤ o`, `Σ a ≤ 1` are not hypotheses of Theorem 4, confirming the proof pass |
| Grounded Replay | Req 1 | `StandingTrace.step`, `grounds_standing`, `grounds_nonempty` | exact; the freshness clause (`Fresh`) is stated and not consumed — the paper's remark that freshness makes the entry unique is about uniqueness, not existence |
| not used by any theorem | Req 2, 3, 6, 11 (for Thm 2–3), compat, `Permit`, `Due`, `Continue`, `Designate`, Lemma 5 | none of these appears in the file except Req 2 as `AnchorStanding` for item 5 | confirmed |

One thing the Lean statement makes visible that the paper leaves implicit: `M` is abstract.
The paper constructs `M_n` from roots and designations; the theorems need only
`matters_mono` and `matters_prior`, which that construction satisfies. Proving that the
construction satisfies them is not done here.

## Fixtures

| # | claim | class | check |
|---|---|---|---|
| F1 | The ownership-only gate admits the rotating-prerequisite trace | LEAN-VERIFIED | `Fixtures.fixA_live_gate_holds` |
| F2 | On that trace matter `a` is live forever, has no work from 2 on, and no prerequisite is a permanent no-route wait — Persistent-Wait's conclusion fails | LEAN-VERIFIED | `fixA_persistent_wait_fails` |
| F3 | The reach gate rejects it, at `n = 2`, issue `b1`, matter `a` | LEAN-VERIFIED | `fixA_reach_gate_fails` |
| F4 | Every other `IssueTrace` field holds on it, so Requirement 12 is what rejects it | LEAN-VERIFIED | `fixA_other_requirements`; `Fixtures.toIssueTrace` shows the fields are exactly the structure |
| F5 | Unqualified route extinction is false: `Routes_1(d) = ∅`, `Routes_2(d) = {t}` | LEAN-VERIFIED | `fixB_routes` |
| F6 | A two-node waiting cycle is work at every position | LEAN-VERIFIED | `fixE_cycle_is_work` |
| F7 | Fixtures C (permanent no-route wait), D (extinction after introduction), F (branch/merge/designate) | FINITE-TEST-SUPPORTED, Python only | `tests/test_fixtures.py` |

## What no entry above claims

That wait responsiveness or non-starvation hold of anything; both are hypotheses. That
the eight semantic judgments have any realization. That the paper's `M_n` construction is
the only one meeting the two abstract fields. That anything about `Permit`, `Due`,
`Continue`, checkers, Proper Exercise, or Legitimate Improvement is established here.
