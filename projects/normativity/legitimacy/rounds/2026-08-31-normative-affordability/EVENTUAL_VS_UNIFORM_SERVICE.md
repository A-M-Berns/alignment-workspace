# Persistence, eventual service, and uniform timeliness

## 1. Three problems, two of which coincide

    persistence            sum_t a_t = infinity ; claims need not be discharged
    eventual full service  every claim is transported, with no uniform deadline
    uniform bounded delay  every claim is transported within one fixed H

The third is strictly stronger than the second. **The first two are equivalent as
existence questions**, under the hypotheses of §2 — an earlier version of this
document claimed a strict separation there and it is withdrawn.

`BOUNDED_DELAY_AFFORDABILITY.md` §4's reading of the `H -> infinity` limit as the
persistence criterion is also withdrawn, for the different reason in §3.

## 2. Persistence and eventual full service are the same existence question

**Theorem EV1.** Fix exogenous date costs `L_s` that are increasing, star-shaped
and vanish at zero; claims `c_t` with each `c_t` finite and `sum_t c_t = infinity`;
fungible service and unlimited deferral. Then

    a persistent affordable schedule exists   <==>   an affordable plan
                                                     discharging every claim exists,

and both are equivalent to `liminf_s L_s(1) = 0`.

*Forward.* Persistence gives `liminf_s L_s(1) = 0`, and by the reference-level
lemma of `SHARP_PERSISTENCE.md` §2 that gives `liminf_s L_s(c) = 0` for every fixed
finite `c`. Enumerate the positive claims and choose service dates `s_0 < s_1 < ...`
with `s_t >= t` and `L_{s_t}(c_t) <= B 2^{-(t+1)}`, which is possible because each
requirement is met at infinitely many dates. Every claim is served and the total
charge is at most `B`.

*Reverse.* Any plan discharging every claim allocates
`sum_s a_s >= sum_t c_t = infinity`, so it is itself a persistent schedule. `square`

**The claim-mass hypothesis is load-bearing.** With `sum_t c_t < infinity` a finite
plan discharges everything while allocating finite total authority, so eventual
service does not imply persistence.

**Existence, not identity.** EV1 is about which schedules *exist*. A persistent
schedule may ignore the claims entirely — it need only spend authority — while some
*other* affordable schedule discharges all of them. The two questions have the same
answer; they are not the same schedule.

**The withdrawn countermodel.** An earlier E2 took `w_{2^k} = 2^-k` with unit
claims and argued that eventual service fails because batching each block onto its
dip costs at least `1/2` per block. That priced one plan and read it as the
minimum. The diagonal of EV1 gives each claim its *own* dip, and the fixture
confirms it: eight claims served on a horizon carrying enough dips, total charge
under `1`, against a block-batching cost of `4`.
`tests/test_timely.py::PersistenceGivesEventualFullService`.

## 3. Uniform timeliness is strictly stronger

**Countermodel E1.** Unit claims at every date; date weights `w_t = 1` except
`w_{2^k} = 4^{-k}`.

*Eventual full service is cheap.* Batch the `2^k` claims arriving in `(2^k, 2^{k+1}]`
onto the dip at `2^{k+1}`, whose weight is `4^{-(k+1)}`. That block costs
`2^k · 4^{-(k+1)} = 2^{-k}/4`, and the total is under `1/2`.

*Every fixed deadline is infinitely expensive.* The gap between consecutive dips is
`2^k`, which exceeds any fixed `H` for `k` large, so all but finitely many claims
have window minimum `1` and `Cost_H = infinity`.

So `lim_{H -> infinity} Cost_H = infinity` while the unbounded-delay cost is under
`1/2`: **the limit of the bounded-delay costs strictly exceeds the cost of the
limit.** `tests/test_joint_service.py::UniformDelayIsStrongerThanEventualService`
pins both sides, including the miss count growing past a thousand at `H = 16`.

The mechanism is that batching needs the whole block to wait for the next dip, and a
uniform deadline forbids waiting a growing amount. Timeliness is not the limit of
timeliness with a large constant.

## 4. Bounded gaps do not close it

An earlier version of this document claimed that bounded gaps between cheap dates
make the three problems coincide, and that a positive density of cheap dates gives
bounded gaps. **Both are withdrawn.** Positive density does not imply bounded gaps;
and, more importantly, bounded gaps do not imply finite timely-service cost.

**Countermodel E3.** `w_{2k} = 1/k` and `w_{2k+1} = 1`, unit claims, `H = 1`. The
cheap dates have gap exactly two and the friction dips to zero, so persistence and
eventual service are both affordable. But every window contains a cheap date of
weight about `1/k`, and

    sum_t min_{s in [t, t+1]} w_s   ~   2 sum_k 1/k   =   infinity ,

so timely service is unaffordable. `tests/test_timely.py::BoundedGapsDoNotSuffice`
pins the gap, the dip, the divergence, and the affordability of the diagonal on the
same sequence.

The lesson is that a window containing a cheap date is not enough — the date has to
be cheap *enough*, and with infinitely many claims each paying a vanishing amount
the sum can still diverge. **No condition on gap size substitutes for the exact
criterion**, which is `BOUNDED_DELAY_AFFORDABILITY.md` D4:

    sum_t c_t · min_{s in [t, t+H]} w_s  <  infinity .

**If the claim stream is finite**, all three are trivially equivalent.

## 5. The corrected hierarchy

    persistence  ==  eventual full service   (  uniform bounded delay ,

the equivalence under EV1's hypotheses and the inclusion strict by E1.

> **Unlimited deferral makes "eventually answer every persistent claim" no harder
> than maintaining divergent service. The substantive Answerability constraint
> enters only when delay itself matters.**

That is scoped to the exogenous, fungible, unlimited-deferral benchmark, and it is
the sharpest thing the round can say about why deadlines are where Answerability
does its work.

`BOUNDED_DELAY_AFFORDABILITY.md` D4's closed form is unaffected — it is a statement
at a fixed `H`. What is withdrawn is the reading of its `H -> infinity` limit as the
persistence criterion.

`SERVICEABILITY_FRONTIER.md`'s critical delay `H*(B)` is also unaffected as a
definition, but it can be `infinity` even when eventual full service is affordable —
which is the honest reading of E1 and is now recorded there.

## 6. What this does not establish

Which of the three an Answerability semantics actually demands; that is the content
of its admissible traces, and the round's position is that it should export them
rather than a quota. EV1 outside its hypotheses: nonfungible service, bounded
deferral, infinite individual claim masses, or policy-dependent costs each break the
diagonal. And EV1 says nothing about *which* schedule a scheduler should run — only
that if one exists, so does the other.
