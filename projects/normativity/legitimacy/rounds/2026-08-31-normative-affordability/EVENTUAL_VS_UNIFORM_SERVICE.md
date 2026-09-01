# Persistence, eventual service, and uniform timeliness

## 1. Three problems, not one

    persistence            sum_t a_t = infinity ; claims need not be discharged
    eventual full service  every claim is transported, with no uniform deadline
    uniform bounded delay  every claim is transported within one fixed H

Each is strictly stronger than the last, and `BOUNDED_DELAY_AFFORDABILITY.md` §4
said the third interpolates to the first as `H -> infinity`. **That is false and is
withdrawn.**

## 2. Uniform timeliness is strictly stronger than eventual service

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

## 3. Eventual service is strictly stronger than persistence

**Countermodel E2.** The same claims with `w_{2^k} = 2^{-k}` — dips too shallow to
carry the block they would have to absorb.

*Persistence holds.* `liminf w_t = 0`, so the geometric tranche construction of
`SHARP_PERSISTENCE.md` S1 allocates without bound on a finite budget. It does not
discharge the claims; it only spends authority.

*Eventual full service fails.* Any plan must carry the `2^k` claims of the `k`-th
block, and the cheapest date available to them costs `2^{-k}` per unit at best, so
each block costs at least `2^k · 2^{-(k+1)} = 1/2` and the total diverges. The
fixture computes the exact block-batching cost as `2, 4, 8` at eight, sixteen and
thirty-two blocks.

So persistence buys unbounded *authority* and not the discharge of the claims that
authority was owed to. That distinction was implicit in the round from the start —
persistence is a statement about the service measure and Answerability is a
statement about claims — and E2 makes it exact.

## 4. When the three coincide

**If the gaps between cheap dates are bounded** by `G`, then every claim's window at
`H >= G` contains a dip, `Cost_H = Cost_infinity` for `H >= G`, and the three
problems agree up to the constant. This is the regime in which the earlier
interpolation claim was true, and it is a real regime — a norm whose friction dips
on a positive density of dates has bounded gaps.

**If the claim stream is finite**, all three are trivially equivalent.

Otherwise they separate, and the separations are in the two directions above.

## 5. What this changes

`BOUNDED_DELAY_AFFORDABILITY.md` D4's closed form is unaffected — it is a statement
at a fixed `H`. What is withdrawn is the sentence reading the `H -> infinity` limit
of that formula as the unconstrained persistence criterion. The corrected statement
is that the formula's limit is the *eventual full service* cost only when the dip
gaps are bounded, and neither equals the persistence criterion in general.

`SERVICEABILITY_FRONTIER.md`'s critical delay `H*(B)` is also unaffected as a
definition, but it can be `infinity` even when eventual full service is affordable —
which is the honest reading of E1 and is now recorded there.

## 6. What this does not establish

Which of the three an Answerability semantics actually demands; that is the content
of its admissible traces, and the round's position is that it should export them
rather than a quota. Whether bounded dip gaps are typical for norms a practice
produces.
