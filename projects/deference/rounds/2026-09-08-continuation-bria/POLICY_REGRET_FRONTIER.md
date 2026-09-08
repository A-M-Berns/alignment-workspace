# The policy-regret frontier — *[repaired by the pressure pass]*

Labels as in `FIXED_HORIZON.md`.  Provisional names: *history-shift discrepancy*,
*three-bridge theorem*, *uniform block recovery*, *catch-up cost*.

## 1. Two layers of return

**A. BRIA-internal, realized.**  For block `k` only the executed controller has a return:

```
G^obs_k ∈ [0, 1]      the gated block average of what was actually run.
```
This is the whole feedback.  The criterion, the records, the wealths and the theorems of
`GROWING_HORIZON.md` §1 consume nothing else.  No counterfactual reward vector is
supplied to the learner, and none is defined by the criterion — exactly as in the paper.

**B. External theorem semantics.**  The theorist declares an interactive environment —
here the environment model of `src/envs.py`, i.e. a rollout `β(H, q, z)` with the
exterior policy `z` fixed — and reads off a **counterfactual block evaluator**

```
Ĝ_k(q; H)      the gated block average controller q would obtain over block k started from H.
```
`Ĝ_k(q; H^α_{t_k}) = G^obs_k` on the block where `q` was executed from the learner's
history; every other value of `Ĝ` is unobserved by the learner.  Own-trajectory value of
a policy `π` is `V_T(π) = Σ_k m_k Ĝ_k(π; H^π_{t_k})` at block boundaries.  Policy regret
and history shift are stated with `Ĝ`; they are theorems *about* the learner, not
quantities the learner computes.  FIX `test_pressure.H_CounterfactualTyping`: on a run
where the comparator is executed on few blocks, `G^obs` exists only there, `Ĝ` is defined
everywhere by the model, the two agree where both exist, and the identity below holds.

The first version of this document said `G_k(π|H^α)` was "realized when tested, undefined
otherwise" and then summed it over every block.  That was the two layers conflated; the
sum is over `Ĝ`.

**Continuation-BRIA never consumes counterfactual rewards; the policy-regret theorem
does.**

## 2. The irreversible-branch impossibility — FIX

`branch_env` (`test_frontier.L_IrreversibleBranch`, `test_pressure.N_IrreversibleBranch`):
at `t = 0` two legitimate irreversible options `A`, `B`; after the good one every action
pays 1, after the other `1/3`; which is good is not visible at `t = 0` (both hypotheses
promise the same prior there).

- A deterministic learner takes one branch; the environment with the other branch good
  gives it `1/3` forever.  Whichever it takes, the hindsight-best legitimate policy gets
  1 per step: gap `(2/3)(T − 1)`, **no learner has sublinear regret against the
  unrestricted legitimate class** (`test_no_learner_escapes`).  A randomizing learner has
  expected regret `(1/3)(T − 1)`.
- The continuation-BRIA is exact on the same run: from the actual history every
  controller's `Ĝ` is `1/3`, every promise is `1/3` and kept, `LEARN = 0`, `SLACK = 0`
  after the branch block; the whole gap is history shift except 2 units of slack at the
  branch block where the blind prior under-promised the untaken branch.

So **continuation-BRIA does not imply policy regret**, for a reason different from the
paper's Appendix C (self-reference): the environment is irreversible, not
self-referential.  An irreversible choice is not "bad"; it puts the policy that took the
other branch outside the class for which regret is achievable.

## 3. The three-bridge theorem — LEAN `regret_decomposition`, `regret_le_of_bounds`

For a policy `π` with a continuation hypothesis `h_π = (π, L)` in the covered class, at a
block boundary `T = S_K`:

```
LEARN_T(π) := Σ_{k≤K} m_k [ L_k − G^obs_k(α) ]                           realized data only
SLACK_T(π) := Σ_{k≤K} m_k [ Ĝ_k(π; H^α_{t_k}) − L_k ]                    external
SHIFT_T(π) := Σ_{k≤K} m_k [ Ĝ_k(π; H^π_{t_k}) − Ĝ_k(π; H^α_{t_k}) ]       external

Regret_T(α, π) := V_T(π) − V_T(α)  =  SHIFT_T + SLACK_T + LEARN_T          (identity)
```
Off a block boundary, `T = S_K + r` with `0 ≤ r < m_{K+1}`, add the boundary term
`Σ_{S_K < t ≤ T} (r_t(π) − r_t(α))`, of absolute value at most `r < M_{K+1}`; under
non-dominance it is `o(T)`.  FIX `test_frontier.RegretDecomposition`,
`test_pressure.H_CounterfactualTyping`.

**Three-bridge theorem** (DERIVED; the algebra LEAN).  If

```
LEARN_T(π) ≤ o(T)      [continuation-BRIA: Theorem 1 under (R)]
SLACK_T(π) ≤ o(T)      [promise recognizability]
SHIFT_T(π) ≤ o(T)      [recoverability]
```
then `Regret_T(α, π) ≤ o(T)`.  Each bridge is one-sided: regret needs an upper bound, so
a promise that overpromises on untested blocks (negative slack) and a learner history that
is *better* for `π` than its own (negative shift) only help.

The dispatch's four-term candidate types as: learning = `LEARN`; finite-horizon truncation
= inside `SLACK` (the tightest sound claim of a plan whose value lies beyond the block is
low); history shift = `SHIFT`; block-boundary/exploration = the boundary term and, for
exploration, inside `LEARN` (the auction's tests are what `Σ m_k (L_k − G^obs_k)` pays
for, bounded by `𝒜_K`).

**The class over which legitimate-policy regret is achievable** is therefore

```
Π_rec,prom  :=  { π legitimate :  h_π covered with (R),  SLACK_T(π) ≤ o(T),  SHIFT_T(π) ≤ o(T) }
```
and the strongest true statement quantifies over it.  The irreversible branch shows the
third condition cannot be dropped; `D_PromiseVersusValue` shows the second cannot.

**History-shift discrepancy** (provisional): `SHIFT_T(π)`, and its absolute form
`B_T(π) := Σ_k m_k |Ĝ_k(π; H^π) − Ĝ_k(π; H^α)|`.  The workspace already has the divergence
in two registers — the phi-regret-bridge round's *residual counterfactual distortion*
(repository replay versus local counterfactual loss) and the local-regret round's finding
that Blum–Mansour's theorem "never constructs the trajectory the comparator would have
produced".  `SHIFT` is the same gap in the continuation register; a new name for the
block-weighted, one-sided form only.

## 4. Recoverability: the weakest condition the theorem consumes

The three-bridge theorem consumes exactly `SHIFT_T(π) ≤ o(T)`, one-sided, along the
learner's actual block starts, per policy.  Everything else is a sufficient schema.

**Uniform block recovery** (one checkable sufficient schema): there is `φ` with
`φ(m)/m → 0` such that for every history `H` the learner can reach and every block start,
`m · (Ĝ_m(π; H^π) − Ĝ_m(π; H)) ≤ φ(m)`.  Then `SHIFT_T ≤ Σ_k φ(m_k) = o(S_K)` whenever
`m_k → ∞` in Cesàro mean.  Instances (FIX `test_frontier.M_Recoverable`,
`test_pressure.M_RecoverableAmendment`):

- **episodic / exact reset**: `φ = 0`.
- **mixing**: `φ = const`; recovered iff the average block length grows — the third use
  of `m_k → ∞`.
- **bounded memory / bounded influence of a finite prefix**: `φ` bounded by memory length
  times reward range; the same case.
- **recoverable amendment — catch-up cost.**  On the persistent amendment with
  investment length `d`, from the learner's `base` the investor's `m`-block value is
  `(m−d)/m`, from its own `expanded` it is 1; the per-block shift is exactly `d` for every
  `m ≥ d` (`M_RecoverableAmendment`).  So a legitimate policy that differs from the learner
  by an amendment it requested earlier has `SHIFT_T ≤ dK = o(S_K)`: the learner can
  always enter `π`'s admissibility state at cost `d`, and growing blocks amortise it.
  Provisional name: **catch-up cost**; it is the theorem-shaped form of recoverable
  admissibility state.  An *irreversible* amendment has no finite catch-up cost and the
  policy that made it is outside `Π_rec,prom`.
- **irreversible branch**: `m (Ĝ_m(B; B) − Ĝ_m(B; A)) = (2/3) m`, `φ(m)/m → 2/3`.

Weaker sufficient forms the theorem also accepts, none developed here: average recovery
along the learner's actual block starts (the aggregate is all that is used); recovery in
expectation for a randomizing learner; policy-class-uniform recovery for a uniform regret
statement.  Whether `SHIFT_T(π)` can be *certified* from inside — by the learner, from
realized data — is OPEN: it contains the unobserved values of `Ĝ`.

## 5. The boundary, stated

- **BRIA result** (this round): the learner's observed `m`-weighted average is
  asymptotically at least the `m`-weighted average of the *promises* of every covered
  continuation hypothesis satisfying (R) — bounded learning against empirically
  accountable, temporally extended continuation claims on the histories the learner
  actually reaches.
- **Policy-regret theorem** (later): the learner performs nearly as well as a legitimate
  continuation policy on that policy's own induced trajectory.  It needs the BRIA result
  plus a computationally accessible near-tight promise for the policy (`SLACK ≤ o(T)`)
  plus recoverability of the policy's own history, in value, from the histories on which
  the learner can test it (`SHIFT ≤ o(T)`).  The irreversible branch shows the third
  cannot be dropped; the vacuous-promise fixture shows the second cannot.
