# Affordability against Answerability's admissible traces

## 1. The real existence question

`SHARP_PERSISTENCE.md` characterizes when *some* divergent allocation is
affordable. Answerability does not accept every divergent allocation as service.
Write

    L_A  =  the set of allocated-service traces Answerability admits

— its deadlines, its bounded-delay requirements, its minimum cumulative service,
whatever the transport plans it will accept impose. The existence question is

    exists a in L_A  with  sum_t L_t(a_t) <= B .

The unconstrained criterion is a **dip** condition. Every constraint below turns it
into something stronger, and the pattern is the same each time: constraining *when*
service must happen replaces a liminf by a sum.

## 2. Bounded delay with a service floor

Partition the dates into windows `B_1, B_2, ...` of width `H`, the deadline. Two
readings of "bounded delay", and they behave completely differently.

**Qualitative — some service in every window.** This does not bite. Allocate an
arbitrarily small `eps_i` in each window, summable, and take the divergent mass from
the dip dates as before. Persistence survives, and so does the criterion of S1.

**Quantitative — at least `alpha > 0` in every window.** This bites hard. Write

    Ľ_i(a)  =  min_{t in B_i} L_t(a) ,

which is again increasing, star-shaped and vanishing at zero, since a minimum of
such functions is one. Serving the floor costs at least `Ľ_i(alpha)` in window `i`,
and spending it at the window's cheapest date attains that.

**Theorem A1.** A per-window floor `alpha` is affordable on budget `B` if and only
if `sum_i Ľ_i(alpha) <= B`. In particular, since
`Ľ_i(alpha) >= alpha Ľ_i(1)` for `alpha <= 1`, a necessary condition is

    sum_i  min_{t in B_i} L_t(1)  <  infinity .

*Proof.* Necessity is the display; sufficiency is to allocate `alpha` at each
window's minimizing date and nothing else. `square`

So:

> **Unconstrained persistence needs the reference cost to dip. Persistence with a
> per-window service floor needs the window minima to be summable.**

That is a genuine strengthening, from `liminf = 0` to `sum < infinity`, and it is
where affordability and service fidelity actually conflict.

**The separation is exact.** Take reference costs pinned at `1` except at
multiples of `16`, where they are `4^-k`. The sequence has `liminf L_t(1) = 0`, so
unconstrained persistence holds; but with windows of width `4`, three quarters of
the windows have minimum exactly `1`, so the window minima are not summable and a
floor of any positive size is unaffordable.
`tests/test_sharp_cost.py::BoundedDelayNeedsSummableWindowMinima` pins the counts
and shows the charge growing linearly with the horizon, against a geometrically
decaying reference where the same floor costs under `1/2`.

## 3. A cumulative service lower bound

Suppose Answerability requires `A_N >= G(N)` for a growth function `G`. By S2 the
cheapest way to hold cumulative authority `G(N)` using dates before `N` is to
concentrate on the best one, so a necessary condition is

    min_{t<N} L_t( G(N) )  <=  B    for every N .

For the sharp charge on its linear branch this reads

    G(N) · min_{t<N} s_t^2  <=  4B ,

so **the required service growth and the friction decay must be reciprocal**: a
demand growing like `G` needs the running minimum depth to fall at least like
`1/sqrt(G(N))`. A linear service demand `G(N) = N` needs `min_{t<N} s_t = O(N^{-1/2})`.

This is the quantitative form of §2's message. Answerability can ask for growth, or
for timeliness, and each converts into a decay rate the norm's friction has to
meet.

## 4. Delay-weighted transport, and the frontier

Deferring a claim from `t` to `s` costs transport error `epsilon(t, s)`, which the
composition theorem carries into the final bound as the residual `eps_r`. The
scheduler therefore faces a genuine trade: the cheap dates are the low-friction
ones, and they may be far from where the claim was owed.

The optimization is

    minimize   sum_{t,s} T(t,s) epsilon(t,s)          transport error
    subject to sum_s T(t,s) = c_t                     every claim placed
               sum_t T(t,s) <= a_s                    feasibility
               sum_s L_s(a_s) <= B                    affordable .

**Proposition A2 (the frontier is real, not merely rhetorical).** With a single
claim per date, an error `epsilon(t,s) = eta (s - t)` linear in the delay, and
reference costs equal to `1` except at multiples of `g` where they are `4^-k`, the
affordable schedules place claims only at the dip dates, so the average transport
error is at least `eta g / 2` — proportional to the dip spacing — while an
error-free schedule serves at every date and costs at least one unit of budget per
date. So the achievable pairs (transport error, lifetime charge) are bounded away
from the origin in both coordinates, and the frontier is parametrized by the dip
spacing.

That is the honest statement available at this level: the two residuals of the
fixed-era theorem are not independently minimizable, and the parameter trading them
is how often enforcement is cheap. A sharper frontier needs a model of how
`epsilon` grows with delay for an actual reason type, which the round does not
have.

## 5. What this changes about the earlier reading

`PERSISTENT_AFFORDABILITY.md` §4 already noted that the sparse optimum "pushes the
burden onto transport stability". §2 makes that precise and slightly worse than it
sounded: under a per-window service floor the dip criterion is not merely strained,
it is replaced by a summability criterion that most dip sequences fail.

The practical consequence for the interface is that **Answerability should export
its admissible traces, not a cumulative quota**, because the affordability question
is settled by *which windows* the service must fall in, and a scalar quota does not
carry that.

## 6. What this does not establish

That any particular Answerability semantics produces one of these constraint
shapes. That A2's frontier is tight. That the transport optimization above is
solvable in general — it is a transportation problem with a nonconvex budget
constraint, since the sublevel set of a sum of concave costs is not convex.
