# The policy-regret frontier

Labels as in `FIXED_HORIZON.md`.  Provisional name: *history-shift discrepancy*.

## 1. Two quantities

At the learner's actual history `H^α_{t_k}`, a continuation test observes

```
G_k(π | H^α_{t_k})        the gated m_k-block average of π started from the learner's history
```
(realized when tested, undefined otherwise).  External policy regret compares the learner
with `π` on the history `π` would itself have produced:

```
V_T(π) = Σ_{t≤T} r_t(H^π)       the own-trajectory value
```
which is never realized unless the learner is `π`.  The two can differ arbitrarily, and
continuation-BRIA is a statement about the first only.

## 2. The irreversible-branch impossibility — FIX

`branch_env` (`test_frontier.L_IrreversibleBranch`): at `t = 0` two legitimate irreversible
options `A`, `B`; after the good one every action pays 1, after the other `1/3`; which is
good is not visible at `t = 0` (both hypotheses promise the same prior there).

- A deterministic learner takes one branch; the environment with the other branch good
  gives it `1/3` forever.  Whichever branch it takes, the hindsight-best legitimate policy
  gets 1 per step, and the gap is `(2/3)(T − 1)`: **no learner has sublinear regret against
  the unrestricted legitimate class** (`test_no_learner_escapes`).  A randomizing learner
  has expected regret `(1/3)(T − 1)`.
- The continuation-BRIA is exact on the same run: from the actual history every
  controller's block value is `1/3`, every sound promise is `1/3`, every promise is kept
  exactly, the learning error is 0.  Continuation competence holds; policy regret is
  linear; the whole gap is the history-shift term of §3 except for one block of slack at
  the branch point where the blind prior under-promised the untaken branch.

So **continuation-BRIA does not imply policy regret**, and no strengthening of the
learner can change that: the obstruction is that testing `B` "from the current history"
cannot reproduce the world in which `B` was taken at `t = 0`.  This is a different reason
from the paper's Appendix C (self-reference makes Hannan consistency unachievable); here
the environment is not self-referential, only irreversible.

## 3. The decomposition — LEAN `regret_decomposition`, FIX `test_identity_is_exact_on_a_generic_run`

For a continuation policy `π` whose hypothesis promises `L_k` at block `k`, and `T = S_K`:

```
V_T(π) − V_T(α)
  =  Σ_k m_k ( G_k(π | H^π_{t_k}) − G_k(π | H^α_{t_k}) )      history-shift      Δ_T(π)
  +  Σ_k m_k ( G_k(π | H^α_{t_k}) − L_k )                     promise slack
  +  Σ_k m_k ( L_k − G_k(α) )                                 learning error
```
plus a boundary term of at most `M_K` when `T` is not a block end.  An identity; every
term exact.  The first two are counterfactual except on tested blocks; the third is
realized.  Growing-Horizon Continuation Competence bounds the third by `o(S_K)` from
above.  The second is the promise-complexity cost (`GROWING_HORIZON.md` §4): zero for a
tight sound promise, the truncation loss for a plan whose value lies beyond the block,
one refutation for a learning hypothesis.  The first is the new term.

The dispatch's four-term candidate — continuation learning, finite-horizon truncation,
history shift, block boundary — types as: learning = the third line; truncation = part of
the slack (a sound block promise for a plan paying beyond the block is low); history shift
= the first line; boundary = the `M_K` term.  Exploration error is inside the learning
term: the auction's tests are what `Σ m_k (L_k − G_k(α))` pays for, bounded by `𝒜_K`.

**History-shift discrepancy** (provisional):
```
Δ_T(π) := Σ_{k≤K} m_k ( G_k(π | H^π_{t_k}) − G_k(π | H^α_{t_k}) ),     B_T(π) := Σ_k m_k |·|.
```
The workspace already has this divergence in two registers.  The phi-regret-bridge
round's *residual counterfactual distortion* is the gap between repository replay and
local counterfactual loss under a frozen environment; the local-regret round's source
audit found that Blum–Mansour's theorem scores the transformed action at the state that
actually obtained and "never constructs the trajectory the comparator would have
produced", so replay is not in the theorem.  `Δ_T` is the same gap in the continuation
register: the theorem of this round scores `π` on the learner's states, and the
own-trajectory statement needs `Δ_T = o(T)`.  No new concept; a new name only for the
block-weighted form.

## 4. Recoverability — what would make `Δ_T = o(T)`

One abstract condition subsumes the dispatch's list.  **Uniform block recovery** for
`π`: there is `φ` with `φ(m)/m → 0` such that for every history `H` the learner can
reach and every block start, `m · |G_m(π | H) − G_m(π | H^π)| ≤ φ(m)`, the second
average taken from `π`'s own history at the same clock time.  Then

```
B_T(π) ≤ Σ_{k≤K} φ(m_k) = o(S_K)      when m_k → ∞ in Cesàro mean,
```
since for any `η` eventually `φ(m_k) ≤ η m_k`.  Instances (FIX `test_frontier.M_Recoverable`):

- **episodic / exact reset**: `φ = 0`; every block starts at the common state and the
  two averages are equal (`test_episodic_reset_makes_history_shift_vanish`).
- **mixing**: `φ = const` (one step in `mixing_env`,
  `test_mixing_recovers_within_one_step`); recovered iff the average block length grows,
  which is the third use of `m_k → ∞`.
- **bounded memory / bounded influence of a finite prefix**: `φ` bounded by the memory
  length times the reward range — the same case.
- **reversible amendments / recoverable endogenous admissibility**: `π` re-requests what
  the learner did not, `φ = d` (the investment length).
- **eventually stable admissibility**: recovers only if the state after stabilisation is
  common, which is one of the cases above or not recoverable.
- **irreversible branch**: `m |G_m(B | A) − G_m(B | B)| = (2/3) m`, `φ(m)/m → 2/3`
  (`test_irreversible_branch_is_not_recoverable`).

**Policy-regret corollary** (DERIVED, conditional).  Under Growing-Horizon Continuation
Competence for a hypothesis of `π` with slack `Σ_k m_k (G_k(π|H^α) − L_k) = o(S_K)` and
uniform block recovery with `S_K/K → ∞`:

```
V_T(π) − V_T(α) ≤ o(T).
```

The recoverability condition is external to the criterion (EXT where asserted of an
environment, FIX where a fixture supplies it) and is the exact consumer assumption.
Whether an abstract quantity like `B_T(π)` can be *certified* from inside — by the
learner, from realized data — is OPEN; `B_T` contains the untested block values.  The
section ends open on that, as the dispatch allows.

## 5. The boundary, stated

- **BRIA result** (this round): the learner cannot asymptotically underperform, in
  `m`-weighted average, any e.c. continuation hypothesis whose contextual promises are
  sound on the leases it is actually granted from the learner's actual histories.
- **Policy-regret theorem** (later): the learner performs nearly as well as the best
  legitimate continuation policy on that policy's own induced trajectory.  It needs the
  BRIA result plus `Δ_T(π) = o(T)` plus a promise for `π` with vanishing slack.  The
  irreversible branch shows the first addition cannot be dropped; the promise-complexity
  examples show the second cannot.
