# Growing-horizon continuation competence — *[repaired by the pressure pass]*

Labels as in `FIXED_HORIZON.md`.  Provisional names: *continuation-promise competence*,
*actual-history continuation competence*, *own-trajectory continuation competence*,
*tested overpromise*, *horizon-stable promise*, *m-detectable advantage*.

## 0. Two returns, one observed

Block `k` has an **observed** return `G^obs_k ∈ [0,1]`: the realized gated block average
of the controller actually executed.  This is all the criterion, the records and the
auction ever see.  An **external** block evaluator `Ĝ_k(q; H)` — the value a declared
rollout semantics assigns to controller `q` started from history `H` — is a theorist's
object; it agrees with `G^obs_k` on the block where `q` was executed from `H`, and it is
otherwise unobserved.  `POLICY_REGRET_FRONTIER.md` §1 fixes the typing.  Everything in §1
below uses only `G^obs`; §2 uses `Ĝ`.

## 1. The theorem, with the promise condition it actually consumes

A continuation hypothesis `h = (q_h, e_h)` makes an accountable contextual claim `e_{h,k}`
at each block; the claim may be wrong.  Let `M_h` be the learner's test set for `h`
(rounds where `h`'s controller is executed under `h`'s declared treatment) and define
`h`'s **weighted record** and **tested overpromise**

```
ℓ^h_K  := Σ_{k ∈ M_h, k ≤ K} m_k (G^obs_k − e_{h,k})
O^h_K  := Σ_{k ∈ M_h, k ≤ K} m_k (e_{h,k} − G^obs_k)_+ .
```
Both are functions of realized data only.

**Theorem 1 — continuation-promise competence** (DERIVED from the weighted criterion;
the paper's Theorem 3 argument with weights and the weakest hypothesis it uses).  Let
`α` be a weighted continuation-BRIA covering `h`.  If

```
(R)   for some C,  ℓ^h_K ≥ −C  for infinitely many rounds K at which α rejects h
```
— exactly the negation of coverage's divergence clause, so in particular if `ℓ^h_K` is
bounded below, in particular if `sup_K O^h_K < ∞` (finite total tested overpromise), in
particular if
`h` overpromises on at most finitely many of its tests, in particular if `h` is sound on
every test — then `α` rejects `h` finitely often, `α^e_k ≥ e_{h,k}` for `k ≥ k_0`, and the
**learning error**

```
LEARN_K(h) := Σ_{k≤K} m_k (e_{h,k} − G^obs_k(α))  ≤  S_{k_0} + Σ_{k≤K} m_k (α^e_k − G^obs_k(α))  =  o(S_K).
```

Proof.  Coverage says: `B_h` finite, or `ℓ^h_K → −∞` along `B_h`.  (R) excludes the
second, so `B_h` is finite; then `LEARN_K = Σ m_k (e_k − α^e_k) + Σ m_k (α^e_k − G^obs_k)`,
the first sum is at most `S_{k_0}`, the second is `o(S_K)` by weighted no
overestimation.  ∎

What the theorem says and does not say.  It compares the learner's observed reward with
the hypothesis's *promises*, not with the controller's value.  A controller worth 1
whose hypothesis promises 0 yields `LEARN ≤ 0` and no competence against 1 (FIX
`test_pressure.D_PromiseVersusValue`).  The first version of this document stated the
conclusion as "cannot underperform a hypothesis whose promises are sound"; that is
Theorem 1 read as a statement about promises, and every sentence that read it as a
statement about the controller's value is withdrawn.

**The promise hierarchy** (FIX `test_pressure.E`, `F`, `G`):

| condition on `h` | Theorem 1 | witness |
|---|---|---|
| sound on every test | yes | the sound hypotheses of every fixture |
| eventually sound: wrong on finitely many tests, bounded total | yes | `F_FiniteOverpromise`: promise 1 on three early tests of a controller worth 2/3, record `−3`, then followed |
| record bounded below (or merely `≥ −C` infinitely often along rejections) | yes — this is (R) | — |
| sublinear tested overpromise, `O^h_K = o(S_K)` but `→ ∞` | **no** | `G_SublinearOverpromise`: overpromise `1/k` per test; a BRIA may test it on a density-zero set with divergent harmonic sum, satisfy coverage as the record tends to `−∞`, reject it elsewhere and obtain nothing there |

So the hierarchy the dispatch hoped for stops at (R): at the criterion level, a
hypothesis whose record diverges *at any rate* may be rejected forever.  The construction
is more forgiving — its wealth `W = A_i + record + (paid < promised)` keeps a slowly
diverging hypothesis in play as long as `A_i(K) + ℓ^h_K` stays above the block's
liability — but that is a property of one auction and one allowance, not of the
criterion, and it is not a theorem here.  A hypothesis that *learns* its promise
(`test_frontier.O_LearningHypothesis`) is the eventually-sound row: one refutation per
state class, then (R).

## 2. Actual-history and own-trajectory competence

With the external evaluator, define for `h = (q, e)` the **promise slack** and, for a
policy `π` with its own trajectory, the **history shift**:

```
SLACK_K(h) := Σ_{k≤K} m_k ( Ĝ_k(q; H^α_{t_k}) − e_{h,k} )
SHIFT_K(π) := Σ_{k≤K} m_k ( Ĝ_k(π; H^π_{t_k}) − Ĝ_k(π; H^α_{t_k}) ).
```

**Theorem 2 — actual-history continuation competence.**  Under (R) and
`SLACK_K(h) ≤ o(S_K)` (one-sided: the promise is not too *loose*; overpromising on
untested blocks only helps this inequality and only hurts (R) if it happens on tests),

```
Σ_{k≤K} m_k ( Ĝ_k(q; H^α_{t_k}) − G^obs_k(α) )  =  SLACK_K + LEARN_K  ≤  o(S_K).
```
FIX `test_pressure.E_VanishingSlack`: promise `1 − 1/(k+1)` for a controller worth 1;
slack `Σ m_k/(k+1) = o(S_K)`; the learner's tail average is exactly 1.

**Theorem 3 — own-trajectory continuation competence.**  Add `SHIFT_K(π) ≤ o(S_K)`:
`Σ m_k (Ĝ_k(π; H^π) − G^obs_k(α)) ≤ o(S_K)`.  This is `POLICY_REGRET_FRONTIER.md`'s
three-bridge theorem (LEAN `regret_decomposition`, `regret_le_of_bounds`).

Existence of a learner for Theorems 1–3 is `WEIGHTED_BRIA.md` §4: for every non-dominant
schedule, uniformly and online.  The theorems themselves need only `S_K → ∞`; the
primitive-time form at non-boundary times needs `M_K/S_K → 0` for the boundary term.

## 3. Which delayed plans become learnable

What a plan gains from growing horizons is that a claim sound at every long enough
horizon eventually competes.

**Definition** (provisional).  A continuation policy `π` has a **horizon-stable promise**
`L(H)` at `H` from horizon `m_0` if for every `m ≥ m_0` its gated `m`-block value from `H`
under the declared treatment is at least `L(H)`; it has an **`m`-detectable advantage**
`δ` over `π'` at `H` if its `m`-block value from `H` exceeds `π'`'s by `δ`.

**Corollary A — fixed horizons are subsumed.**  If `h` promises a horizon-stable
`L_k = L(H_{t_k})` from `m_0` and `m_k ≥ m_0` for `k ≥ k_1`, then Theorem 1 gives
`Σ m_k (L_k − G^obs_k(α)) ≤ o(S_K)`; with `SLACK ≤ o(S_K)` Theorem 2 gives competence
against `π`'s actual-history value.  Not "every fixed-`m` advantage transfers": a
controller whose `m`-block value is high and whose `2m`-block value is low has no
horizon-stable claim above the latter.

**Corollary B — fixed finite delay is learned** (FIX `B_FixedHorizonRescue`,
`D_HorizonTooShort`).  Persistent benefit after `d` investment steps: the investing
controller's `m`-block value from `base` is `(m−d)/m`, horizon-stable from `m_0 ≥ d`, and
from the benefit state it is 1.  With `m_k → ∞` the hypothesis promising `(m_k − d)/m_k`
from `base` and 1 from `expanded` is sound with slack 0, so Theorem 2 gives the learner's
average `→ 1`.  Renewable benefit with cycle `d + e`: `⌊m/(d+e)⌋ e/m → e/(d+e)`, slack
`O(K(d+e)) = o(S_K)` once the average block length grows.  Any fixed `d` is learned; no
fixed `m` learns every `d` (`C_MinimalHorizon`: `m > 3d/2` against `work`).

**Corollary C — uniformly-often detectable advantages are captured.**  If at every block
start `π` has a horizon-stable promise `L_k` and the learner's estimates fall below
`L_k − δ` on a set of blocks of positive `m`-weighted density, Theorem 1 is contradicted.

**The truncation error** is promise slack: a plan with long-run average `v` and cycle `c`
has `m`-block value at least `v − c/m`, and its tightest sound claim has slack
`≤ Σ_k c = cK`, which is `o(S_K)` iff `S_K/K → ∞`.  So `m_k → ∞` is needed twice: for
the claim to be sound at all (`m_k ≥ d`) and for its slack to be negligible.

## 4. Where fixed `m` fails, exactly

Families on `investment_env` (mechanism `D_HorizonTooShort`): benefit at `m+1` (`d = m`:
the invest block from `base` is worth 0, not `m`-detectable); benefit at `2m` (the same,
and the following block would see it only after an investment nothing scores);
environment-dependent finite delay `d(H)` (fixed `m` fails whenever `d(H) ≥ m` on block
starts of positive weighted density; a growing schedule with `m_k > 3d(H_{t_k})/2`
eventually catches each); growing delay `d_k → ∞` (the schedule must outrun it, which
nothing in the criterion supplies); an irreversible amendment whose value appears much
later (the previous case on the trajectory where the value appears,
`POLICY_REGRET_FRONTIER.md` on the other).

## 5. Promise recognizability versus controller complexity

The comparator class of Theorems 1–2 is a class of *hypotheses*: pairs `(controller,
contextual claim)` in the covered class, with (R) and small slack.  It is not a class of
controllers.  The paper's Theorem 3 has the same shape (efficiently identifiable option
*and* e.c. lower bound); Theorem 4 relaxes the claim to one unrefuted on e.c. averages.
Three cases, stated at the level the round can support:

1. **Controller code and promise code are distinct objects** (conceptual, PAPER-shaped).
   The controller "always `a`" whose reward at step `t` is the `t`-th binary digit of `√2`
   (FIX `test_frontier.N_EasyPolicyHardValue`) illustrates the *type* distinction: the
   pointwise value is the digit itself, and the claim that survives 4000 steps is the
   averaged `2/5`.  **No complexity separation is claimed**: the digits of `√2` are
   computable, the round names no resource class in which the promise is harder than the
   controller, and the paper's π-digit example is a stance on pseudorandomness relative to
   a class, not a theorem.  The first version's "hard value" wording is withdrawn to this.
2. **A hypothesis that learns its promise** (FIX `test_frontier.O_LearningHypothesis`):
   eventually sound after one refutation per state class; inside Theorem 1 by the
   hierarchy of §1.  The class is broader than pointwise-sound claims.
3. **What genuinely limits recognition** is the paper's Theorem 2 diagonal: an
   `O(g)`-computable learner is diagonalised by an `O(g)`-computable hypothesis that
   promises 1 and recommends whatever the learner does not.  Read for promises: a bounded
   learner cannot be required to follow every good computable plan, because "good" is not
   a property it can check from the plan's code.  What it can be required to follow is a
   plan *with a claim that survives its own tests* — case 2's route, or Theorem 4's
   averaged claims.  That is what `H_cont` says, and it is the paper's stance made
   explicit, not a separation theorem.

## 6. What is not established

- Competence against a controller's *value* without a slack condition; Theorem 1 is
  about promises (`D_PromiseVersusValue`).
- Any criterion-level result under sublinear-but-divergent tested overpromise
  (`G_SublinearOverpromise`); the construction's tolerance is not a theorem.
- Any own-trajectory statement without `SHIFT ≤ o(S_K)`; any certificate of it from
  realized data.
- A complexity separation between controllers and promises.
- A rate; a weighted Theorem 4.
