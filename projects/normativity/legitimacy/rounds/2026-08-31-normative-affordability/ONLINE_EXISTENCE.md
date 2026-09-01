# Causal scheduling: there is no online penalty for persistence

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
never revises, and needs no regularity on `q` beyond the liminf. It wastes a factor
of at most `4` against an offline optimum that knew where the dips were, because
`theta_k` may overshoot the friction actually encountered — and overshooting only
helps, since a smaller `q_t` buys *more* authority for the same tranche.

`tests/test_persistence.py::TheCausalSchedulerLosesNothing` checks all four parts:
every trigger contributes at least `B^2/4`, the budget is never exceeded, a
floored friction triggers only finitely often (three times at floor `1/4`), and a
decaying friction triggers at every threshold.

**Many reasons.** Run one copy per reason on tranche `B 2^{-(r+1)}`. Each copy's
criterion is unchanged, so every individually persistable reason is persistently
served by the product rule, with no coordination and no shared state. This is the
constructive form of the persistence region's closure under countable unions.

## 3. Why the online problem is easy here

Two structural facts, and neither is generic to online scheduling.

**The resource is not perishable.** An unspent tranche remains available forever.
There is no cost to waiting, so the classic online tension — commit now or lose the
opportunity — is absent.

**The payoff is convex in the spend and the constraint is a stock.** Spending a
tranche at friction `q` buys `(b/q)^2`, so the *value* of waiting for a smaller `q`
grows quadratically while the *cost* of waiting is zero. A greedy threshold rule
therefore cannot be beaten by more than a constant.

Both facts fail as soon as the requirement is a positive *rate* rather than
persistence, because then delay does cost: authority accumulated late does not
raise `liminf A_N/N`. So the online question is easy for the property the
composition theorem consumes, and open for the quantitative one.

## 4. Adversarial arrivals defeat a fair scheduler

The rule above is not fair in any usual sense — it spends everything on rare dates
and nothing in between — and that is necessary.

**Countermodel O2.** A scheduler that insists on allocating a fixed positive
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

**Rates, not persistence.** O1 is about `sum a_t = infinity`. Whether a causal
scheduler can match an offline one's *growth rate* of `A^r_N` is open, and §3 says
the easy argument does not survive there.

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
