# Theorem and countermodel ledger

Every label is one of the dispatch's allowed evidence classes.

| ID | Statement | Evidence | Boundary / witness |
|---|---|---|---|
| PC-D1 | `PracticalCert(e,s,Pi_s;M,epsilon) := Lambda_es(Pi_s) <= M d_s + epsilon` is the minimal theorem-facing practical interface. | **proposed definition/interface** | The Progress proof consumes this inequality; semantic authentication is external. |
| PC-D2 | `JointPracticalAdequacy(s,E_s,Pi_s) := forall e in E_s, PracticalCert(e,s,Pi_s;M_es,epsilon_es)`. | **proposed definition/interface** | Every edge names the same response receipt. |
| PC-P1 | Nonnegative proxy transport and response adequacy yield `M=LC`, `epsilon=L epsilon_0+epsilon_resp`. | **lean-proved** | `proxy_le_defect`, `proxy_route`; semantic proxy premises remain hypotheses. |
| PC-P2 | The adequate-set route yields `M=D kappa`, `epsilon=epsilon_ad+D theta`. | **lean-proved** | `adequate_set_route`; finite menu, probability weights, bounded losses, off-set coupling. |
| PC-P3 | One-sided deterministic calibration yields regret `<=2r+eta`. | **lean-proved** | `one_sided_argmax_transfer`. |
| PC-P4 | One-sided calibration on the realized support yields randomized regret `<=2r+eta`. | **lean-proved** | `one_sided_randomized_argmax_transfer`; finite menu. |
| PC-P5 | A uniform adapter certifies every edge at every quote iff one common distribution is epsilon-adequate at a zero-defect quote. | **lean-proved** | `bundle_certifiable_iff_zero_defect_adequate`; assumes nonnegative multipliers/defects and existence of a zero-defect quote. |
| PC-P6 | Disjoint adequate sets with off-set loss at least `D` force the sum of two anchored expected losses to be at least `D`. | **lean-proved** | `disjoint_adequate_sets_force_loss`; exact three-response witness attains equality. |
| PC-P7 | Sharing displayed value coordinates forces two authenticated scalar values to disagree by at most the sum of their calibration radii. | **lean-proved** | `shared_coordinates_bound_disagreement`; scalar-coordinate route only. |
| PC-P8 | Regret dominance for a zero-regret response of anchored loss `D` forces `epsilon_resp>=D`. | **lean-proved** | `regret_dominance_vacuous_on_forbidden_optimum`. |
| PC-P9 | Two adequate-set failure-mass bounds imply intersection mass at least `1-theta_1-theta_2`. | **lean-proved** | `union_bound_two`; necessary condition only. |
| PC-W1 | Adequate-set constants `(0,1/2)` certify the half mixture for `e1`. | **exact-witness** | Python and `adequate_set_route_inhabited`. |
| PC-W2 | Two exposures may occupy one feasible `K_s` while no common response has loss below `1/2` on both. | **exact-witness** | Exact Farkas inequality; Lean sum-loss lower bound and attained half mixture. |
| PC-W3 | A common randomized response may meet tolerance `1/2` when no deterministic response does. | **exact-witness** | Three-response fixture. |
| PC-W4 | The value and adequate-set routes can have crossing affine bounds. | **exact-witness** | `(2,1)` versus `(10,0)`, crossing at `d=1/8`. |
| PC-W5 | Two-sided calibration can be strictly stronger than the one-sided premises actually used. | **exact-witness** | Radii `1/2` and `1/10`. |
| PC-W6 | Membership `v* in V` is not used by directed calibration algebra. | **exact-witness** | `V=[2/5,3/5]`, `v*=7/10`, `zeta=3/10`; no authentication conclusion. |
| PC-W7 | Charging separately certifiable edges to one non-common response makes the column Progress inequality false. | **exact-witness** | Realized `1/2`, claimed `0`; `honest_column` rejects the edge. |
| PC-W8 | Omitting off-set coupling, bounded off-set loss, or adequate-set loss control destroys the adequate-set conclusion. | **exact-witness** | Exact rational necessity tests. |
| PC-A1 | Anchoring and causal/evaluation validity of `Lambda_es`. | **ambient assumption** | Practical semantics owner; not established by the inequality. |
| PC-A2 | Pre-response authenticity of the response receipt and constants. | **ambient assumption** | Required to prevent post-selection/relabeling. |
| PC-O1 | A complete certificate calculus for infinite or history-dependent response spaces. | **open** | Would require ecology-specific measurability and causal semantics. |
| PC-O2 | A complete finite joint-compatibility decision procedure integrated with the transport checker. | **open** | Farkas-style exact refutations are only a sufficient fixture here. |

## Lean audit

Declarations are in
`Workspace.Normativity.Contrib.PracticalCertificate`.  The module imports the landed
`NormativeInductor` lemmas rather than restating them.  Every declaration has a
`#print axioms` line.  The build output reports only allowed core axioms; exact output
is recorded by rerunning the command in `REPORT.md`.

## What this ledger does not promote

No paper-derived interface is a registered workspace claim merely because it appears
here.  No exact fixture proves a general theorem.  The Lean results prove algebra under
named hypotheses and do not establish their semantic premises.
