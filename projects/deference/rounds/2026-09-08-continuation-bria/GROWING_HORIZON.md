# Growing-horizon continuation competence

Labels as in `FIXED_HORIZON.md`.  Provisional names: *horizon-stable promise*,
*m-detectable advantage*.

## 1. The theorem

**Growing-Horizon Continuation Competence** (DERIVED from the weighted criterion; the
algebra of the construction LEAN; the criterion's consequence is the paper's Theorem 3
argument with weights).

Let `(m_k)` be a declared schedule with `S_K → ∞`, and `α` a weighted continuation-BRIA
covering a class `H_cont` of continuation hypotheses.  Let `h ∈ H_cont` make **sound
contextual promises on its tests**: whenever `h`'s controller is executed through the gate
for block `k` from the learner's actual history, the realized block average satisfies
`G_k ≥ L_k := h^e_k`.  Then

```
liminf_K  Σ_{k≤K} m_k (G_k(α) − L_k) / S_K  ≥ 0.
```

Proof.  `h`'s weighted record on every test set is `Σ m_k (G_k − L_k) ≥ 0`, so `h` is
rejected finitely often: `α^e_k ≥ L_k` for `k ≥ k_0`.  Then
`Σ_{k≤K} m_k (G_k − L_k) = Σ m_k (G_k − α^e_k) + Σ m_k (α^e_k − L_k) ≥ −o(S_K) − S_{k_0}`.
∎

Existence of such an `α` for the full e.c. class is `WEIGHTED_BRIA.md` §4: exactly when
`m_K / S_K → 0`.  The theorem itself needs only `S_K → ∞`; non-dominance is the price of
having a learner to apply it to.

**Primitive-time form.**  With `ℓ_t := L_k` for `t` in block `k`,
`liminf_T (1/T) Σ_{t≤T} (r_t − ℓ_t) ≥ 0` at block boundaries (LEAN
`sum_blocks_eq_weighted`), and at other `T` the error is at most `M_K / S_K → 0` under
non-dominance — which is a second place the condition is needed, and the reason the
dispatch's `max_{j≤K} m_j / Σ_{j≤K} m_j → 0` is the right non-dominance to state.

## 2. Which delayed plans become learnable

The theorem is about promises; what a plan gains from growing horizons is that a promise
sound at every long enough horizon eventually competes.

**Definition** (provisional).  A continuation policy `π` has a **horizon-stable lower
bound** `L(H)` at a history `H` from horizon `m_0` if for every `m ≥ m_0` its gated
`m`-block average from `H` is at least `L(H)`.  It has an **`m`-detectable advantage**
`δ` over `π'` at `H` if its `m`-block average from `H` exceeds `π'`'s by `δ`.

**Corollary A — fixed horizons are subsumed.**  If `π`'s hypothesis promises a
horizon-stable lower bound `L_k = L(H_{t_k})` from `m_0` and `m_k ≥ m_0` for `k ≥ k_1`,
then `α`'s primitive-time reward is asymptotically at least the `m_k`-weighted average of
`L_k`.  (Blocks before `k_1` contribute a constant.)  This is not "every fixed-`m`
advantage transfers": a controller whose value over `m` steps is high and over `2m` steps
is low has no horizon-stable bound above its `2m` value, and the theorem does not credit
it.  What transfers is what is sustainable.

**Corollary B — fixed finite delay is learned** (FIX `B_FixedHorizonRescue`,
`D_HorizonTooShort` for the mechanism at fixed `m`).  Persistent benefit after `d`
investment steps: the investing controller's `m`-block value from `base` is `(m−d)/m`,
horizon-stable from any `m_0 ≥ d` with bound `(m_0 − d)/m_0`, and from the benefit state it
is 1.  With `m_k → ∞`, for every `η > 0` the hypothesis promising `(m_k − d)/m_k` from
`base` and 1 from `expanded` is sound and eventually promises above `1 − η`; the learner's
average is at least `1 − η` in the limit.  Renewable benefit with cycle `d + e`: the
`m`-block value from `base` is at least `⌊m/(d+e)⌋ e / m → e/(d+e)`, so the learner reaches
`e/(d+e) − η` for every `η`.  Any fixed `d` is learned; no fixed `m` learns every `d`
(`C_MinimalHorizon`: `m > 3d/2` is needed against `work`).

**Corollary C — uniformly-often detectable advantages are captured.**  If at every
block start `π` has a horizon-stable bound `L_k` and the learner's own eventual estimates
fall below `L_k − δ` on a set of blocks of positive `m`-weighted density, the theorem is
contradicted.  So the learner's `m`-weighted average shortfall against any such `L` is
zero in the limit.

**The truncation error.**  A plan with long-run average `v` and cycle length `c` has
`m`-block value at least `v − c/m` from a cycle boundary; the loss against `v` over the
first `K` blocks is at most `Σ_k c = cK`, which is `o(S_K)` iff the *average* block
length `S_K/K → ∞`.  So `m_k → ∞` is needed twice: to make the promise sound at all
(`m_k ≥ d`) and to make the per-block truncation negligible in primitive time.

## 3. Where fixed `m` fails, exactly

Families (all on `investment_env`; the mechanism is `D_HorizonTooShort`):

- **benefit at `m+1`** — `d = m`: the invest block from `base` is worth 0; not
  `m`-detectable; the fixed-`m` learner is myopic.
- **benefit at `2m`** — `d = 2m − 1`: the same, and the block after it would see the
  benefit only if the learner had invested in the previous block, which nothing scores.
- **environment-dependent finite delay** `d(H)` — fixed `m` fails whenever `d(H) ≥ m` on a
  set of block starts of positive weighted density; a growing schedule with
  `m_k > 3 d(H_{t_k})/2` eventually catches each.
- **growing delay** `d_k → ∞` — no fixed `m`; a growing `m_k` needs `m_k / d_k` bounded
  away from `3/2` eventually, otherwise the sound promises stay at 0.  Growth of the
  schedule must outrun growth of the delay; nothing in the criterion supplies that.
- **irreversible amendment whose value appears much later** — this is the previous case
  if the learner is in the trajectory where the value appears, and
  `POLICY_REGRET_FRONTIER.md` if it is not: an irreversible act moves every later block
  start, and no lease from the other side of it sees the value.

`m`-detectable advantage isolates the point: fixed-horizon competence credits exactly the
advantages visible in one block from the actual history.  The term is used above and not
canonised beyond this round.

## 4. Promise complexity versus policy complexity

The comparator class of the theorem is the class of *hypotheses*: efficiently
computable `(controller, contextual promise)` pairs whose promises are sound on their
tests.  It is not the class of efficiently computable controllers.  The paper's Theorem 3
has the same shape (efficiently identifiable option *and* e.c. lower bound), and so does
Theorem 4 (e.c. means).  Three cases:

1. **Easy policy, hard value** (FIX `test_frontier.N_EasyPolicyHardValue`; the canonical
   instance is the paper's π-digit option).  The controller "always `a`" pays the `t`-th
   binary digit of `√2`; the pointwise value is the digit, and a promise equal to it is
   the sequence itself.  The hypothesis promising `2/5` is not refuted over 4000 steps and
   its record grows.  So the learner competes with the *averaged* promise, not the
   pointwise one — Theorem 4's class, whose promises need only be unrefuted on the
   learner's e.c. test sets.
2. **A hypothesis that learns its promise** (FIX `test_frontier.O_LearningHypothesis`).
   Promise := minimum block average observed on its own past leases from the same state,
   less a margin.  It must be tested to learn, and a test needs a bid above the
   incumbent's, so it starts optimistic (prior 1), is refuted once (record `−1`), and
   thereafter promises `2/3 − 1/10` from `base`, which it keeps on every lease; its record
   then rises by the margin per lease.  The same hypothesis with prior 0 is never tested
   and never learns.  So a learning hypothesis pays for its education in exactly one
   refutation per state class, and this is inside the theorem: the record stays bounded
   below, coverage holds, and once the promise is sound the guaranteed-option argument
   applies from that round.  The class is therefore broader than pointwise-sound
   promises: promises sound *from some round on* suffice, and promises whose record is
   bounded below suffice for coverage.
3. **A good plan with no accessible recognition.**  A controller whose block values are
   1 on a set of blocks that every e.c. selection sees as having density 0 has no e.c.
   promise above 0 that survives its own tests, and the learner is not required to follow
   it.  This is the paper's stance made exact by Theorem 2's diagonalisation: an e.c.
   learner obliged to follow every good computable plan would be diagonalised by a plan
   whose goodness it cannot check.  A bounded learner should be required to compete with
   cases 1 and 2 and not with case 3, and that is what `H_cont` says.

Unavoidable, then, and exactly the paper's; broadenable by case 2 to promises that
become sound after finitely many refutations, and, by Theorem 4's route, to promises that
are correct on e.c. averages.

## 5. What is not established

- Any own-trajectory statement: the promises are about blocks from the learner's actual
  histories, and the theorem compares the learner with what those blocks would have
  returned on those histories only.  `POLICY_REGRET_FRONTIER.md`.
- Anything about a benefit hidden behind an irreversible act the learner did not take.
- Any future-principal value semantics: `G_k` is a generic bounded realized return.
- A rate, or a weighted Theorem 4.
