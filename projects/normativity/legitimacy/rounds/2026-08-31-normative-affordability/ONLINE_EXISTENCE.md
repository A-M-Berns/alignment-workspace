# Causal scheduling: no online penalty for persistence, none available for rate

Scoped to the **conservative** charge and an **exogenous** friction sequence, as
`PERSISTENT_AFFORDABILITY.md` is; `CLOSED_LOOP_EXISTENCE.md` says what survives when
the friction depends on the policy.

## 1. The online problem

The offline characterization of `PERSISTENT_AFFORDABILITY.md` assumes the friction
sequence `q^r_t` is known in advance. It is not. The realistic timing is that
`q^r_t` — the row's worst live exclusion depth times the date's engine scale — is
computable at date `t`, before the allocation is chosen and before the market maker
picks a price. A causal scheduler sees `q^r_t` and must commit `a^r_t` immediately,
with no knowledge of whether a smaller friction is coming.

That is an online problem with an obvious threat: a scheduler that spends on a
friction of `2^-3` may find `2^-30` arriving next date, and a scheduler that waits
may find nothing smaller ever arrives.

## 2. There is no gap

**Theorem O1.** A causal scheduler achieves persistent affordable service exactly
when an offline one can — that is, iff `liminf_t q_t = 0` — and the rule is
explicit.

*The rule.* Hold a threshold index `k`, starting at `0`, with thresholds
`theta_k = 2^-k` and tranches `b_k = B 2^{-(k+1)}`. On the first date with
`q_t <= theta_k`, allocate

    a_t = ( b_k / q_t )^2 ,

which spends exactly the tranche, and advance `k`. Allocate nothing otherwise.

*Proof.* The charge is `q_t sqrt(a_t) = b_k`, and `sum_k b_k = B`, so the schedule
is affordable at every horizon. When the `k`-th tranche is spent,
`q_t <= theta_k = 2^-k` and `b_k = B 2^{-(k+1)}`, so

    a_t = (b_k/q_t)^2 >= (B 2^{-(k+1)} / 2^{-k})^2 = B^2/4 ,

a contribution bounded below by a constant independent of `k`. The rule triggers
infinitely often iff for every `k` some later date has `q_t <= 2^-k`, which is
`liminf q_t = 0`. So `A_N -> infinity` exactly in that case. Necessity is the
offline direction of P1, which no policy can evade. `square`

The scheduler is oblivious in the strongest sense: it never estimates the future,
never revises, and needs no regularity on `q` beyond the liminf.

**It has no competitive guarantee, and the earlier claim of a factor of `4` is
withdrawn.** At level `k` the rule's tranche is `B 2^{-(k+1)}`; if a friction
`q << 2^-k` then appears it buys `(B 2^{-(k+1)}/q)^2` where an offline scheduler
would have bought `(B/q)^2`. The ratio is `4^{-(k+1)}`, which tends to zero. §3a
shows no rule does better.

`tests/test_persistence.py::TheCausalSchedulerLosesNothing` checks all four parts:
every trigger contributes at least `B^2/4`, the budget is never exceeded, a
floored friction triggers only finitely often (three times at floor `1/4`), and a
decaying friction triggers at every threshold.

**Many reasons.** Run one copy per reason on tranche `B 2^{-(r+1)}`. Each copy's
criterion is unchanged, so every individually persistable reason is persistently
served by the product rule, with no coordination and no shared state. This is the
constructive form of the persistence region's closure under countable unions.

## 3a. No online rule has a positive competitive ratio

**Theorem O2.** For cumulative authority under the conservative charge, no causal
rule achieves a competitive ratio bounded below by any `rho > 0` against the
offline optimum.

*Proof.* Two dates already cap the ratio at `1/4`. Date one has friction `1`; the
rule commits `c <= B` without knowing whether a second date follows. If the run
stops, it holds `c^2` against an offline `B^2`. If a date of friction `eps` follows,
it holds at most `c^2 + ((B-c)/eps)^2` against `(B/eps)^2`, a ratio tending to
`((B-c)/B)^2` as `eps -> 0`. The minimum of the two is maximized at `c = B/2` and
equals `1/4`.

For the general bound take `n` dates with frictions `delta^i` and let the adversary
stop after any of them. Writing `c_i` for the commitment at stage `i`, the earlier
stages contribute at most `(n-1) B^2 delta^2 / delta^{2i}` to the stage-`i` holding,
so a ratio of `rho` at every stopping point forces
`c_i^2 >= (rho - (n-1) delta^2) B^2`. Choosing `delta` with `(n-1)delta^2 < rho/2`
gives `c_i >= B sqrt(rho/2)` at every stage, so `sum_i c_i >= n B sqrt(rho/2) > B`
for `n` large — more than the budget. `square`

`tests/test_sharp_cost.py::NoConstantCompetitiveRatio` pins the two-date bound at
exactly `1/4`, the two degenerate commitments, and the cascade's contradiction.

**So the correct statement of O1 is binary.** There is no online penalty for the
*property* "persistence is achievable", and no positive competitive ratio for the
*amount* of authority accumulated. The right comparison is the qualitative one, and
the composition theorem consumes exactly that: it needs `A^r_N -> infinity`, not a
rate.

## 3. Why the online problem is easy here

Two structural facts, and neither is generic to online scheduling.

**The resource is not perishable.** An unspent tranche remains available forever.
There is no cost to waiting, so the classic online tension — commit now or lose the
opportunity — is absent.

**The payoff is convex in the spend and the constraint is a stock.** Spending a
tranche at friction `q` buys `(b/q)^2`, so the *value* of waiting for a smaller `q`
grows quadratically while the *cost* of waiting is zero. A threshold rule can
therefore always afford to wait for the next dip, which is what makes the
qualitative property attainable — and, by O2, is not enough for any quantitative
guarantee, since the same convexity is what lets an offline optimum outperform it
without bound.

The first fact fails as soon as the requirement is a positive *rate*, because then
delay does cost: authority accumulated late does not raise `liminf A_N/N`. So the
online question is settled for the property the composition theorem consumes, and
negatively settled for the amount.

## 4. Adversarial arrivals defeat a fair scheduler

The rule above is not fair in any usual sense — it spends everything on rare dates
and nothing in between — and that is necessary.

**Countermodel O3.** A scheduler that insists on allocating a fixed positive
authority `a_0 > 0` at every date, or on splitting each date's tranche equally
among the currently live reasons, fails on the friction sequence that is `1`
everywhere except on a sparse set. At friction `1` the charge for `a_0` is
`sqrt(a_0)` per date, so the budget is exhausted after `B/sqrt(a_0)` dates and the
scheduler allocates nothing thereafter — `A_N` bounded — while the threshold rule
runs forever on the same sequence.

The general statement is that **any scheduler with a positive floor on its
per-date allocation is defeated by a friction sequence bounded away from zero on a
set of full density**, by the necessity half of P1 applied to the dates it insists
on serving. Persistence requires the freedom to do nothing.

That is worth recording as a normative fact and not only a scheduling one: a
service discipline that guarantees every reason some attention *every* date is
strictly weaker than one that guarantees unbounded attention *eventually*, and only
the second is affordable against a norm whose friction does not decay.

## 5. What remains open

**Rates, not persistence.** O1 is about `sum a_t = infinity`, and O2 settles the
quantitative question in the negative: no causal scheduler matches an offline one's
accumulated authority within any constant factor. Whether some weaker comparison —
additive, prefixwise, or against a restricted adversary — admits a guarantee is
open.

**Unobservable friction.** O1 assumes `q_t` is computable at date `t`. The worst
live exclusion depth requires enumerating the live worlds against the row, which
the enforcement round computes exactly for small fragments and calls combinatorial
in the world count. A scheduler with only an upper estimate of `q_t` is safe but
may miss dips; one with a lower estimate is unsafe. The estimation error is
therefore one-sided in a useful direction and the theorem survives with `q_t`
replaced by any predictable upper bound, at the cost of triggering less often.

**The signed class.** O1 is a theorem about the conservative charge.
`SIGNED_VS_CONSERVATIVE.md` shows the signed class is strictly larger, and no
online rule for it is offered, because the drift a scheduler can guarantee there is
unknown.

**Arrivals.** Reasons arriving over time are handled by the geometric tranche
split, which requires committing a tranche to each reason at its arrival. Whether a
scheduler that does not know how many reasons will arrive can do better than a
fixed geometric split — or whether it needs to — is open.
