# Fixed horizon: the macro reduction and what it buys

Labels: **PAPER** (`BRIA_SOURCE_AUDIT.md`), **DERIVED**, **LEAN**
(`lean/Workspace/Deference/Contrib/ContinuationBRIA.lean`), **FIX** (`tests/`), **EXT**,
**OPEN**.

## 1. The macro process

Fix `m ≥ 1`.  Primitive time `t`, macro-round `k` starting at `t_k = (k−1)m`.  From the
actual history `H_{t_k}` (the primitive state, or the whole record; the fixtures use a
finite state with time-dependent admissibility):

- **Menu.** `DP'_k` is a finite set of terms naming `m`-step contingent controllers
  `q : (state, step index, time) → action`; the fixtures draw from a finite controller
  library, and in general any finite set of programs of bounded length is finite.
  Membership is a syntactic check.  The set of *all* contingent controllers over finite
  alphabets is finite but exponential in `m`; nothing requires the menu to be it.
- **Wrapper.** `Exec^G_m(H, q)` runs `q` for `m` primitive steps.  At each step `q` sees the
  actual state and the step index (so it is contingent, not open-loop); its proposal goes
  through the gate `G`; an admitted proposal is executed, a refused one becomes the
  inquiry step `⊥` (reward 0, state unchanged) — the truncation of the decision-theory-bill
  round's §2.8, made into a step rather than an abort so that every execution has a
  return.  The exterior (principal responses, corrections, amendments, settlement
  arrivals) is the environment's own time-dependence and runs regardless of the lease
  (`src/envs.py`, `revoke_at`).
- **Reward.** `r'_k = G^m_k(q) = (1/m) Σ_{j<m} r_{t_k + j} ∈ [0,1]` for the controller
  actually executed.  Any declared bounded block functional normalised to `[0,1]` serves.

Nothing else is primitive.  The block return of an unexecuted controller is not defined,
exactly as the paper leaves counterfactual rewards undefined.

## 2. The reduction is definitional — DERIVED

**Fixed-Horizon Reduction.**  `(DP'_k, c'_k, r'_k)_k` is a decision problem sequence in
the sense of §2 of the paper: each `DP'_k` is finite, `c'_k ∈ DP'_k`, `r'_k ∈ [0,1]`, and
`DP'_{k+1}` depends on the history produced by `c'_1, …, c'_k`, which §2 permits.  A
hypothesis for it is a map from macro-histories to `(controller, promise)`.  Every
definition (1–7) and theorem (1–4) of the paper applies verbatim with `t := k`, because none
of them inspects the internal structure of an option or of a reward.

There is no theorem to prove.  Three typing facts carry the content:

1. **Endogeneity is not what was missing.**  The paper already lets `DP_{k+1}` depend on
   `c'_k`; an admissibility process that changes with authorized acts is an instance.  What
   the paper's criterion lacks is credit for a reward that arrives *after* the round in
   which its cause was chosen; the block puts the cause and the effect into one round
   whenever the effect arrives within `m` steps.
2. **What a controller sees.**  The controller is a function of the within-lease history.
   A hypothesis is a function of the whole macro-history.  So the pair "hypothesis at
   `k`, controller for block `k`" is a stateful decision procedure: state across blocks
   lives in the hypothesis, state within a block in the controller.
3. **Interruption.**  The gate may refuse at any step, the exterior may change
   admissibility at any step; neither breaks the process, because the wrapper always
   returns a block average.  Whether a promise about `Exec^G_m(H, q)` is kept is then an
   ordinary empirical question on the actual trajectory.

**Complexity.**  Per macro-round: one evaluation of each active hypothesis (which outputs a
term and a number) plus `m` primitive steps of controller evaluation and gating.  The
paper's `O(g(k) q(k))` bound is in macro-time; in primitive time `t = mk` it is the same
bound with a factor `m` for the wrapper.

**Primitive-time translation** (LEAN `blockAverage_eq`, `sum_range_mul_eq`).
`(1/K) Σ_{k≤K} G_k = (1/(mK)) Σ_{t ≤ mK} r_t` exactly; at a time `T` that is not a block
boundary the two averages differ by at most `m/T`.  So every macro-time limit statement is a
primitive-time limit statement for equal blocks.  The Reduction test
(`test_one_step_is_the_m_equals_one_case`) shows the same auction code at `m = 1` with
single-action controllers *is* the paper's construction, and duration and block weighting
coincide there.

## 3. Fixed-Horizon Continuation Competence — PAPER + DERIVED

**Statement.**  Let `α` be a BRIA for the macro process covering the e.c. hypotheses.
Suppose that for every `k` there is a controller `q_k ∈ DP'_k`, efficiently identifiable
from `DP'_k` and the history, and an e.c. `L_k ∈ [0,1]`, such that whenever `q_k` is the
executed controller of block `k`, `G^m_k(q_k) ≥ L_k`.  Then

```
liminf_K (1/K) Σ_{k≤K} (G_k(α) − L_k) ≥ 0,
```
equivalently `liminf_T (1/T) Σ_{t≤T} (r_t − ℓ_t) ≥ 0` with `ℓ_t := L_k` for `t` in block `k`.

**Proof.**  Theorem 3 applied to the macro process; the primitive form by
`blockAverage_eq` and the `m/T` boundary bound.  The hypothesis `(q_k, L_k)` is a
continuation hypothesis whose promise is sound *on its own tests from the actual
history*; nothing is assumed about `q_k` off those tests.

What the theorem needs, exactly: (i) the promise is a function of the actual history at
the block start (it may be as contextual as it likes); (ii) it lower-bounds the *gated*
block average on the tests — or, weaker, the hypothesis's record on the learner's test set
is bounded below (`GROWING_HORIZON.md` §1, condition (R)); (iii) `q_k` and `L_k` are in
the covered class.  What it does not need: that `q_k` is legitimate, that the environment
is stationary, that any untested block return exists.  What it does not give: competence
against the *value* of `q_k` — the conclusion compares with `L_k`, and a vacuous `L_k`
yields a vacuous conclusion (`test_pressure.D_PromiseVersusValue`).

## 4. The amendment fixture, exactly

`src/envs.py`, `investment_env(d, e)`: the decision-theory-bill process with rewards
divided by three, `d` investment steps, and either a persistent benefit (`e = None`, the
benefit state absorbing) or a renewable one (`e` harvest steps, then back to `base`).
`d = 1`, persistent, is the existing fixture; its `2H − 3` becomes `(2H − 3)/3`.

**A. One-step BRIA** — the prompt's premise corrected, in three registers (FIX
`test_fixed_horizon.A_OneStep`, `test_pressure.C_CriterionVersusConstruction`).
*[repaired by the pressure pass: criterion, construction and fixture are separated.]*

*CRITERION — what every one-step BRIA covering the e.c. class must do on the existing
fixture (`d = 1`, persistent).*  Let `h = (request, 1)`, which never outpromises `α` at a
round where `α^e = 1`.  If `α` is at `base` on a set of rounds of positive upper density,
then no overestimation forces `α^e < 1` on a positive-density subset of them (with
`α^e = 1` on all `base` rounds of density `p`, the average overestimation is at least
`2p/3`), so `h` is rejected infinitely often and must be tested infinitely often — and
each test is the investment.  If `α` is at `base` only on a density-zero set, it may
estimate 1 there, never reject `h`, and never invest again; and an `α` that never returns
to `base` after entering the absorbing benefit state is never obliged to invest again
either.  So the exact quantified statement is: **a BRIA cannot remain at `base` on a set
of positive density; it either invests infinitely often or leaves `base` for good, and
between those it may run sparse excursions.**  The first version's "every one-step BRIA
invests infinitely often" is withdrawn to this.

*The decision-theory-bill learner is not a BRIA.*  It never chooses `request` while `h`
outpromises it at every round with `α^e ≤ 1/3`: coverage fails.  Item 86's "myopic gated
learner" is an argmax, not a bounded inductive learner, and the `2H − 3` it loses is a fact
about that argmax.

*CONSTRUCTION — what the wealth auction does.*  With the ecology `{work, invest, stay}` it
requests finitely often — twice in the run of `test_auction_invests_once_and_stays`,
because after the first investment `invest` has spent its wealth, `stay` cannot yet
afford its bid and `work` wins the state back — and once a sound hypothesis at `expanded`
holds wealth `≥ 1/3` it never returns to `base`.  The count is an artefact of the
ecology's wealths, not of the criterion.

*FIX — the exact simulated ecologies.*  `test_existing_fixture_one_step_auction_invests`:
the tail of 500 rounds is at `expanded` at reward 1.

- With a three-step persistent investment (`d = 3`) the auction with the ecology
  `{work, invest, continue, stay}` stays at `base` for 3000 rounds: the `continue`
  hypothesis needs wealth above `4/3` to finance two consecutive `continue` wins, and
  every isolated one-step test it wins (whenever its wealth passes `1/3`) pays out its
  whole wealth-bounded bid, so it never accumulates the run.  No two consecutive rounds
  are ever won by it.  Whether it eventually escapes depends on the enumeration order of
  the hypotheses (a `continue` hypothesis with more allowance than the `request`
  hypothesis outruns the drain); the criterion neither forbids nor requires it.
- With a *renewable* benefit (`d = 1, e = 2` or `d = 2, e = 4`) the auction is myopic
  (average below `0.37` against the investor's `2/3`), and this is DERIVED for the
  construction, not an accident of the ecology: no one-step claim can attribute a harvest
  reward to the `request` that caused it, so `request` is chosen only as a test of a
  hypothesis that overpromised at `base`, each such test costs that hypothesis its bid,
  and a sound hypothesis bids `1/3` there.  Hence the number of `request` rounds by time
  `K` is at most `3 𝒜_K + O(1)`, of density zero (`test_attention_bound_on_investing_actions`;
  the identity is `WEIGHTED_BRIA.md` §5).  At the criterion level, a BRIA that mostly
  follows the investor also exists (estimate `2/3`, test `work`-claims sparsely).
- The criterion *permits* myopia in every case, the existing fixture included: the
  auction restricted to `base` rounds, with `α^e = 1` and `α^c = work` at every
  non-`base` state, never rejects a continuation or stay hypothesis there, overestimates
  only on the density-zero set of non-`base` rounds, and covers every e.c. hypothesis at
  `base` by the paper's own argument.  It returns to `base` after every forced excursion.
  (Stated, not implemented; it is the paper's construction with a two-line override.)

So: on the exact existing fixture the criterion forces the investment to be tried
whenever the learner keeps returning to `base`, and the auction keeps it; the loss the
fixture records belongs to a learner that is not a BRIA.  The criterion itself is silent
on keeping a benefit, and it cannot see a benefit that needs more than one step to reach
or that must be re-bought: there the failure is exactly temporal credit assignment.

**B. Fixed-horizon rescue** (FIX, `B_FixedHorizonRescue`).  `m = 2` on `d = 1` persistent:
the sound macro-hypothesis for the investing controller promises `1/2 > 1/3` from `base`,
keeps it, and the auction obtains 1 from the second block on.  On `d = 1, e = 2`, `m = 2`:
the contextual promises at the three phases of the cycle are `1/2, 1/2, 1`, each kept
exactly, and the primitive-time average is exactly `2/3`.

**C. Minimal `m`** (FIX, `C_MinimalHorizon`).  The investing controller's `m`-block value
from `base` is `(m − d)/m` (persistent; also renewable while `m ≤ d + e`).  It exceeds
`1/3` iff `m > 3d/2`, so the minimal horizon is `⌊3d/2⌋ + 1`; on the existing fixture,
`m = 2`.  At `m = 3d/2` exactly the values tie and the tie-break decides.

**D. Benefit beyond `m`** (FIX, `D_HorizonTooShort`).  `d = 2, e = 4`, `m = 2`: the invest
block from `base` is worth 0 and the macro auction stays myopic (average below `0.37`);
`m = 4` makes it worth `1/2` and the cycle is learned at exactly `2/3`.

Conclusion of the section: **endogenous admissibility is not the hard problem; credit
assignment at the testing granularity is**, and for a benefit that arrives within a known
`m` the paper's own theorem, retyped, is the whole answer.

## 5. What is not established

- Any statement about a benefit that arrives after the block (`GROWING_HORIZON.md`).
- Anything about the value of a controller on histories other than the learner's
  (`POLICY_REGRET_FRONTIER.md`).
- That the finite menu contains a good controller; Theorem 3 quantifies over supplied
  `q_k`.
- Any rate.  The paper's guarantees are limits, and so are these.
