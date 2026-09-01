# Online bounded-delay service: the gap reappears

## 1. Why waiting stops being free

`ONLINE_EXISTENCE.md` O1 showed that persistence has no online penalty, and §3
there gave the reason: the unspent budget is imperishable, so a threshold rule can
always wait for the next cheap date at no cost.

Under a deadline that reason evaporates. A claim arriving at `t` must be served by
`t + H`, so waiting past the window is not deferral but default. The scheduler must
commit before it knows whether a cheaper legal date is coming, and this is a
genuine ski-rental tension rather than a free option.

## 2. The smallest separation

One unit claim, legal dates `1` and `2`, linear costs. `L_1 = 1` is known at date
`1`; `L_2` is revealed only at date `2` and is either `eps` or `K`. The scheduler
commits a fraction `theta` at date `1` and the remainder at date `2`.

**Theorem OS1.** No commitment fraction bounds the competitive ratio.

*Proof.* Online cost is `theta + (1 - theta) L_2` and offline is `min(1, L_2)`. If
`L_2 = eps`, the ratio is at least `theta / eps`; if `L_2 = K`, it is at least
`(1 - theta) K`. Driving `eps -> 0` and `K -> infinity` forces `theta = 0` and
`theta = 1` respectively, so no fixed `theta` survives both. `square`

At `eps = 1/1000` and `K = 1000` the best fraction on a rational grid still leaves a
ratio above `400`, and the two pure strategies give exactly `1000` each.
`tests/test_bounded_delay.py::TheOnlineDeadlineGap`.

**Contrast.** For unconstrained persistence the *qualitative* property survived
online and only the ratio failed. Here even the qualitative property can fail: with
budget `B` between the online cost and the offline cost, an offline scheduler
services the stream and every online one exhausts the budget. The deadline turns a
quantitative gap into a feasibility gap.

## 3. What an online rule can and cannot know

The scheduler at date `s` knows the claims that have arrived, their deadlines, the
current date weight, and not the future weights. Three consequences.

**The claim stream is not the difficulty.** Claims arriving is information gained,
not lost; the difficulty is entirely the unknown future costs.

**Deadline pressure is monotone.** A claim's remaining window shrinks by one each
date, so the decision is forced at the deadline. Any rule is therefore a stopping
rule per claim, and OS1 is the two-point instance of that stopping problem.

**Estimates are one-sided in a useful direction.** As in `ONLINE_EXISTENCE.md` §5,
a predictable *upper* bound on the date weight keeps every guarantee and only makes
the rule spend earlier. A lower bound would be unsafe.

## 4. What would rescue a guarantee

Three hypotheses, each of which makes the problem tractable and none of which the
round establishes.

**A known bound on the weight range.** If `w_s in [w_-, w_+]` with a known ratio
`kappa = w_+/w_-`, the natural rule — serve at the first legal date whose weight is
within `sqrt(kappa)` of `w_-`, and at the deadline otherwise — is `sqrt(kappa)`-
competitive by the standard ski-rental balance. The ratio degrades as the range
widens, which is why OS1's unbounded range admits nothing.

**Stochastic weights with a known law.** Then the per-claim stopping problem is an
optimal-stopping problem with an explicit threshold, and the competitive question
becomes a regret question.

**Predictable weights.** If `w_s` for the whole window is computable at the claim's
arrival — which is plausible when the exclusion depth is determined by the settled
record and the volume bound is a declared schedule — the problem is offline within
each window and `BOUNDED_DELAY_AFFORDABILITY.md` D4 applies directly, per claim.

The third is the one worth checking against the traderized construction, because
the enforcement round's contract states the volume bound as a declared quantity
`C^tf_n` computable from the belief history. If the whole window's weights are
predictable at the claim's arrival, **there is no online problem at all** — and
that is the most likely resolution, which is why this document does not develop the
competitive theory further.

## 5. What this does not establish

Whether the window's weights are in fact predictable at arrival; that depends on
whether the live-world set at dates `t+1, ..., t+H` is determined at `t`, which is
false on the empirical settlement channel and plausible on the deductive one — the
same split `CLOSED_LOOP_EXISTENCE.md` §3 draws. That the `sqrt(kappa)` rule is
optimal; the balance is standard and the optimality is not checked. Any multi-claim
online theorem: OS1 is a single-claim separation and the interaction between claims
competing for the same cheap date is untouched.
