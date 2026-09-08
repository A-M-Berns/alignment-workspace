# Countermodels and fixtures A–O

All exact (`fractions.Fraction`), run by `tests/run.py` (37 tests, under a second).
Environments in `src/envs.py`; the auction in `src/bria.py`.  Rewards of the
decision-theory-bill process divided by 3: work `1/3`, invest `0`, benefit `1`.

| fixture | test | what it shows | class |
|---|---|---|---|
| **A** myopic amendment failure | `test_fixed_horizon.A_OneStep` (5 tests) | On the existing fixture the one-step auction invests and keeps the benefit; the learner that loses `2H−3` is not a BRIA.  With a three-step investment the auction stays myopic (a continuation hypothesis's capital is drained by isolated one-step tests; no two consecutive wins).  With a renewable benefit the auction is myopic by the attention bound: at most `3𝒜_K + 1` investing actions in `K` rounds. | FIX; DERIVED for the bound |
| **B** fixed-horizon rescue | `B_FixedHorizonRescue` | `m = 2` learns the persistent amendment (average 1) and the renewable cycle at exactly `2/3` with contextual promises `1/2, 1/2, 1`, each kept. | FIX |
| **C** minimal horizon | `C_MinimalHorizon` | invest's `m`-block value from `base` is `(m−d)/m`; minimal `m = ⌊3d/2⌋+1`; existing fixture: 2.  Renewable `d=2,e=4`: values `0, 1/3, 1/2` at `m = 2, 3, 4` (`m = 3` ties). | FIX |
| **D** horizon too short / one-step pseudo-test | `D_HorizonTooShort`; `test_lease.D_PseudoTest` | `m = 2` misses a `d = 2` benefit (average below 0.37), `m = 4` learns it (exactly `2/3`).  A sound promise `1/2` is scored below `1/2` by every early withdrawal of control (`5/18` after one step), and at most `1/3` for any prefix shorter than the investment, whatever follows. | FIX |
| **E** anti-corrigible hard commitment | `test_lease.E_HardCommitment` | Ungated lease executes three prohibited actions after a revocation at `t = 3`, return `5/6`; gated lease refuses them, return `1/3`. | FIX |
| **F** gated lease | `test_lease.F_GatedLease` | Legitimate controller: gated = ungated (transparency).  Hacking controller: every step refused, return 0, promise refuted without a violation.  Same controller and lease, principal revoking at `2`, `5`, or never: returns `1/6`, `2/3`, `5/6`, each the sound contextual promise. | FIX; LEAN `trajGated_eq_traj_of_admitted` |
| **G** biased policy testing | `test_lease.G_BiasedTesting` | `a` beats `b` in both contexts; testing `a` on hard and `b` on easy steps records `3/10` vs `9/10`. | FIX (PAPER App. D, dynamic form) |
| **H** contextual-promise repair | `test_lease.H_ContextualPromiseRepair` | Contextual promises compare within the context; `a` outpromises `b` every step, both records 0, average `13/20`; a context-free promise for `a` loses `7/10` per hard step. | FIX |
| **I** long-test monopoly | `test_weighted.I_Monopoly` | Unweighted macro-BRIA on `m_k = 2^{⌊√k⌋}`: a waiting liar is covered and refuted, macro overestimation below `0.08`, and holds `0.31, 0.375, 0.43` of primitive time at `K_0 = 100, 256, 625` (tends to 1).  Duration charge: never wins, overestimation `≤ 0`, average `3/4`. | FIX; DERIVED asymptotics |
| **J** allowance too slow | `test_weighted.J_Starvation` | `m_k = k`, paper's allowance: liar rejected 400 times, tested never, `A_2(400) < 2`.  Replenishing allowance: tested at `1, 2, 4, 12, 44, 171`, record below `−200`, weighted overestimation below `1/100`. | FIX |
| **K** feasible schedule | `test_weighted.K_FeasibleSchedule` | `m_k = ⌊log₂k⌋+1`, `A = i^{-2}⌊√k⌋^{-1}`: `A_1(K) − m_K` increasing, proof bounds hold, ratio below `1/1000` at `10⁵`. | FIX; DERIVED asymptotics |
| dominance | `test_weighted.Dominance` | `m_k = 2^k`: at every liar test the weighted overestimation exceeds `1/5` and the block is at least half of all time. | FIX; LEAN `dominant_block_lower_bound` |
| algebra | `test_weighted.Algebra` | wealth identity exact under both charges, wealths nonnegative; macro vs primitive averages differ (`0` vs `→ δ`); bounded horizons rescale to the ordinary criterion. | FIX; LEAN `wealth_sum_eq`, `wealth_nonneg` |
| **L** history-shift impossibility | `test_frontier.L_IrreversibleBranch` | Blind prior at the branch; learner takes `A`, environment makes `B` good; continuation competence exact (every promise kept, learning error 0); regret `(2/3)(T−1)`, all history-shift but 2 units of slack at the branch block.  No deterministic learner escapes. | FIX |
| decomposition | `test_frontier.RegretDecomposition` | `V(π) − V(α) = Δ + slack + learning` exact on a generic run. | FIX; LEAN `regret_decomposition` |
| **M** recoverable environment | `test_frontier.M_Recoverable` | Episodic reset: the two block values coincide.  Mixing: they differ by exactly one step per block, `Δ/T ≤ 1/m`.  Irreversible branch: differ by `(2/3)m`. | FIX |
| **N** easy policy, hard value | `test_frontier.N_EasyPolicyHardValue` | Controller paying the `t`-th bit of `√2`; promise `2/5` unrefuted over 4000 steps (record above 300). | FIX (PAPER Thm 4's class) |
| **O** learning hypothesis | `test_frontier.O_LearningHypothesis` | Min-observed-minus-margin promise; must start optimistic to be tested; refuted once (record `−1`), then promises `2/3 − 1/10` from `base` and keeps it; the pessimistic prior is never tested. | FIX |
| reduction | `test_fixed_horizon.Reduction` | `m ≡ 1` with single-action controllers: duration and block weighting give identical runs; equal-block average identity. | FIX; LEAN `blockAverage_eq` |

Fixtures A, D, I and L are the negative results the round rests on; B, F, H, J
(replenishing), K, M and O are the positive witnesses.  The dispatch's A ("one-step
BRIA can rationally remain myopic") is established for the criterion in every case and
for the construction in the three-step and renewable cases, and is *false* for the
construction on the existing one-step fixture.
