# Bounded-delay transport: feasibility

## 1. The problem

Claims `c_t >= 0` arrive at date `t`. A plan `T(t,s) >= 0` places their mass:

    sum_s T(t,s) = c_t ,     sum_t T(t,s) <= a_s ,     t <= s <= t + H .

Two questions with different answers, and the round needs both. This document
answers the first: **given** a service profile `a`, is there a plan?
`BOUNDED_DELAY_AFFORDABILITY.md` answers the second, where `a` is chosen.

The first is what `SERVICE_TRANSFER.md`'s conditions `(T1)` and `(T2)` consume, so
this section replaces the prose around them with a construction.

## 2. The interval condition

**Theorem BD1.** A plan exists if and only if for every interval `[u, v]`

    sum_{t=u}^{v} c_t   <=   sum_{s=u}^{v+H} a_s .

*Necessity.* Mass arriving in `[u,v]` cannot be served before `u` or after
`v + H`.

*Sufficiency.* The bipartite graph has interval neighbourhoods
`N([u,v]) = [u, v+H]`, so it has the consecutive-ones property and the
Gale–Hoffman feasibility condition need only be checked on sets whose
neighbourhoods are unions of pairwise disjoint intervals; for such a set the
condition is the sum of the conditions for its maximal runs, and each run is an
interval. `square`

**Prefixes are not enough.** With `c = (0, 1)`, `a = (1, 0)` and `H = 0`, both
prefix conditions hold — `0 <= 1` and `1 <= 1` — and the interval `[1,1]` fails,
because service cannot run backwards. So the popular summary `C_N <= A_{N+H}` is
necessary and not sufficient, and the two-sided family is the right one.
`tests/test_bounded_delay.py::IntervalFeasibility`.

## 3. First-in-first-out is optimal and complete

**Theorem BD2.** Serving the oldest outstanding claim first is optimal: a plan
exists if and only if FIFO leaves no claim outstanding when it reaches age `H`.

*Proof.* Suppose a feasible plan serves claim `j` at `s_j` and an earlier claim
`i < j` at `s_i > s_j`. Then `s_j >= j >= i` and `s_j <= s_i <= i + H`, so `s_j` is
legal for `i`; and `s_i >= s_j >= j` with `s_i <= i + H <= j + H`, so `s_i` is legal
for `j`. The two service dates may therefore be exchanged, and repeating the
exchange sorts any feasible plan into FIFO order without changing the capacities
used. `square`

Since the deadlines here are uniform, FIFO and earliest-deadline-first coincide.
`fifo_misses` and `interval_condition` are checked to agree over a family of
instances.

**In backlog form.** BD2 says exactly that the *age-`H`* backlog is identically
zero under FIFO. That is the checkable form, it runs in one pass, and it is what a
scheduler would actually monitor.

## 4. What this replaces

`SERVICE_TRANSFER.md`'s Lemma E1 built a FIFO plan from bounded backlog and left
the delay bound conditional on a window service floor. BD1 and BD2 supersede that:
feasibility is exactly the interval condition, FIFO constructs the plan whenever
one exists, and the delay bound is the deadline itself rather than a derived
quantity. The transport conditions `(T1)` and `(T2)` are therefore *constructed*
in this model rather than assumed.

`(T3)`, the stability inequality, is untouched — it is a claim about the reason,
not about the schedule, and `SERVICEABILITY_FRONTIER.md` is where the deadline
finally buys something for it.

## 5. What this does not establish

That the claim process is known in advance; BD1 is an offline characterization and
`ONLINE_SERVICEABILITY.md` is where the causal version goes. That deadlines are
uniform — non-uniform deadlines keep the interval structure only if the windows
are nested or ordered, and the exchange argument of BD2 uses `H` uniform. That
service is fungible: a claim satisfied only by a particular *kind* of later
service is outside this model, and is the general case
`SERVICE_ADMISSIBLE_EXISTENCE.md` keeps as admissible traces.
