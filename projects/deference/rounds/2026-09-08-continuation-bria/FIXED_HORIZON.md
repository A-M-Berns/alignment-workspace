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
single-action controllers has identical runs under duration and block weighting.  At
`m ≡ 1` that code is the paper's auction with its allowance reindexed by one round and
an initial endowment (`WEIGHTED_BRIA.md` §3): the same bids and winners, a different
statement of *when* the subsidy is credited.

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

`src/envs.py`, `investment_env(d, e, sticky)`: the decision-theory-bill process with
rewards divided by three, `d` investment steps, and either a persistent benefit
(`e = None`) or a renewable one (`e` harvest steps, then back to `base`).  `d = 1`,
persistent, `sticky=True` is the existing fixture (its `2H − 3` becomes `(2H − 3)/3`);
with `sticky=False`, the default, `work` at `expanded` returns to `base`.

**A. One-step BRIA** — the prompt's premise corrected, in three registers (FIX
`test_fixed_horizon.A_OneStep`, `test_pressure.C_CriterionVersusConstruction`,
`test_final.B_SparseTestMyopicBRIA`, `test_final.C_AuctionContrast`).
*[Final correctness pass: the criterion register is rewritten; the pressure pass's
"positive density" claim is withdrawn.]*

*Two variants of the one-step fixture.*  The decision-theory-bill fixture keeps the
state under `work` (its transition map returns the state for any action other than
`request`/`hack`), so there `base → expanded` has no path back: the amendment is
**sticky**.  This round's `investment_env(d = 1)` lets `work` at `expanded` return to
`base` by default: the amendment is **revocable**.  `sticky=True` reproduces the
original.  The two behave differently at the criterion level.

*CRITERION — what every one-step BRIA covering the e.c. class must do.*  Let
`h = (request, 1)` at `base`.  Coverage requires: either `h` is rejected finitely often,
or `h`'s record tends to `−∞` along its rejection rounds — which needs `h` to be tested
infinitely often, and nothing more: the tests may be a set of density zero, and each
test contributes exactly `−1`.  Hence:

- *Sticky (the exact original).*  If `α` stayed at `base` forever, `base` would have
  density 1, no overestimation would force `α^e < 1` on a positive-density set of
  `base` rounds, `h` would be rejected infinitely often, hence tested — and one test
  leaves `base` for good.  At `expanded` the sound claim `(expanded, 1)` has record
  `≥ 0` on every test set, so it is rejected finitely often, `α^e ≥ 1` for all but
  finitely many rounds, and no overestimation forces average reward `→ 1`.  **On the
  exact original fixture every BRIA is competent.**
- *Revocable.*  An agent that runs the published auction on `base` rounds and, at
  `expanded`, chooses `work` with estimate 1 is a BRIA (proof below) and is
  asymptotically myopic: it is at `base` on a set of density tending to 1, rejects `h`
  on almost every `base` round, tests `h` on a sparse infinite set at which its record
  tends to `−∞`, and returns to `base` after each test.  FIX
  `test_final.B_SparseTestMyopicBRIA`: over 4000 rounds, 92 tests at growing gaps,
  record `−92`, `base` density `0.977`, average overestimation `0.023`, average reward
  `0.326`; the `stay` claim is never rejected because `α^e = 1` at `expanded`.  The same
  agent on the sticky fixture is stuck at `expanded` with estimate 1 and reward `1/3`,
  overestimation `2/3`, and is not a BRIA there.  **On the revocable variant the
  criterion permits asymptotic myopia.**  So the one-step criterion is already too weak
  for dynamic competence: it forces only that an outpromising claim be tested infinitely
  often, and a claim about `request` at `base` is refuted by every test.

  Proof that the composite agent is a BRIA (DERIVED from the paper's Theorem 1).  The
  `base` rounds form a decision problem sequence in the paper's sense (menu
  `{work, request}`, rewards determined by the choices), and the auction run on that
  subsequence is a BRIA for it: no overestimation relative to the number of `base`
  rounds, coverage of every e.c. hypothesis restricted to `base` rounds with the
  auction's wins as test set.  At `expanded` rounds `α^e = 1`, so no hypothesis is
  rejected there.  The `expanded` rounds are exactly the rounds after a win by a
  `request`-recommending hypothesis at `base`; each such win costs its winner a bid of at
  least `1/3` (the sound `work` claim's bid) and returns 0, so their number by time `K`
  is at most `3𝒜_K + O(1)`, of density zero (`WEIGHTED_BRIA.md` §5).  Total overestimation
  is the `base`-auction's `o(#base)` plus `2/3` per `expanded` round, hence `o(T)`.
  Coverage of an arbitrary e.c. `h'`: its rejection rounds lie in `base` rounds, where
  the `base`-auction covers it.  ∎

*The decision-theory-bill learner is not a BRIA on either variant.*  It never chooses
`request` while `h` outpromises it at every round with `α^e ≤ 1/3`: coverage fails.  Item
86's "myopic gated learner" is an argmax, not a bounded inductive learner, and the
`2H − 3` it loses is a fact about that argmax.

*CONSTRUCTION — what the wealth auction does* (FIX `test_final.C_AuctionContrast`).  With
the ecology `{work, request, stay}` and allowance `1/(i²√k)` it reaches `expanded` and
keeps it: one request on the sticky original, two on the revocable variant (after the
first, `request` has spent its wealth, `stay` cannot yet afford its bid and `work` wins
the state back; once `stay` holds `1/3` the state never returns).  The counts are
artefacts of the ecology's wealths.  So on the one-step fixture the construction happens
to be competent where the criterion permits myopia; that is a property of the auction's
capital dynamics, not of bounded inductive rationality.

*FIX — the multi-step and renewable ecologies*, where the construction's temporal credit
assignment fails more robustly:

- With a three-step persistent investment (`d = 3`) the auction with the ecology
  `{work, invest, continue, stay}` stays at `base` for 3000 rounds: the `continue`
  hypothesis needs wealth above `4/3` to finance two consecutive `continue` wins, and
  every isolated one-step test it wins (whenever its wealth passes `1/3`) pays out its
  whole wealth-bounded bid, so it never accumulates the run.  No two consecutive rounds
  are ever won by it.  Whether it eventually escapes depends on the enumeration order of
  the hypotheses (a `continue` hypothesis with more allowance than the `request`
  hypothesis outruns the drain); the criterion neither forbids nor requires it.
- With a *renewable* benefit (`d = 1, e = 2` or `d = 2, e = 4`) the auction is myopic
  (average below `0.37` against the investor's `2/3`), DERIVED for the construction: no
  one-step claim can attribute a harvest reward to the `request` that caused it, so
  `request` is chosen only as a test of a hypothesis that overpromised at `base`, each
  such test costs that hypothesis its bid, and a sound hypothesis bids `1/3` there.
  Hence the number of `request` rounds by time `K` is at most `3 𝒜_K + O(1)`, of density
  zero (`test_attention_bound_on_investing_actions`).  At the criterion level, a BRIA
  that mostly follows the investor also exists (estimate `2/3`, test `work`-claims
  sparsely).

So: the one-step *criterion* forces testing, not adoption — asymptotic myopia is
permitted whenever the amendment can be revoked, and forced competence on the sticky
original is an accident of absorption, not of credit assignment.  The one-step
*construction* keeps the persistent benefit and fails on multi-step and renewable
investments.  What removes the weakness at the criterion level is a sound claim about
the whole investment: at `m = 2` the macro claim `(invest, 1/2)` from `base` has record
`≥ 0`, so a macro-BRIA must estimate at least `1/2` at `base` and, by no overestimation,
invest on all but a density-zero set of `base` rounds, on both variants.  That is
temporal credit assignment at the testing granularity.

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
