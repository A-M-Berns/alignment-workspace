"""Deriving the service condition from a bounded-resource scheduler.

The round below isolated a liveness premise and **assumed** it:

```text
S1   sum_t o_t(c) = infinity  =>  sum_t u_t(c) = infinity
```

for an open, undefeated, registered challenge. No rate, no deadline, no
fairness, no guarantee the criticism wins. This module asks whether a concrete
bounded-resource mechanism *derives* it.

```text
o_t(c)  adjudicative opportunity represented at t, in [0,1]
u_t(c)  service delivered at t,  0 <= u_t(c) <= o_t(c)
budget  sum_c u_t(c) <= B at every t
```

## Two mechanisms, and they are not equally strong

**Positive share.** Give every live challenge a persistent weight `w(c) > 0` with
`sum_c w(c) <= B` and serve `u_t(c) = w(c) o_t(c)`. Then

```text
sum_t u_t(c) = w(c) sum_t o_t(c) = infinity
```

and the budget holds because `o_t(c) <= 1`. Feasible for **countably many**
challenges with a summable schedule such as `w(c_n) = B 2^{-n-1}`. This derives
S1 outright and needs service to be **fractionally divisible**.

**Least-recently-served.** If service is atomic -- one challenge per step, all of
its available opportunity or none -- weights are unavailable. A scheduler that
serves the challenge with the oldest last-service time *among those with
opportunity now* also derives S1, and needs no divisibility. It does need the
scheduler to be **adaptive**: a fixed dovetailing order fails against an
adversary who presents opportunity only when the schedule is elsewhere, which is
`SR8`.

## What actually has to persist

Not the weight. `sum_t w_t(c) o_t(c) = infinity` follows from
`inf_t w_t(c) > 0`, so the invariant is a **positive floor**, not a pinned value:

```text
W1   an open undefeated challenge's service entitlement has a positive infimum
```

This is strictly weaker than the round below's episode pinning, and deliberately
so. Reprioritisation stays available -- a challenge's share may fall by any
finite factor, repeatedly -- and what is forbidden is driving the floor to zero.
`SR6` shrinks a share geometrically without ever setting it to zero, and that is
already fatal.
"""
from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import Callable, Mapping, Optional, Sequence


BUDGET = 1.0


@dataclass(frozen=True)
class Chal:
    """A registered challenge, for scheduling purposes only.

    `born` is its registration position and `closed` the position at which it was
    defeated, addressed or transferred. Service obligations run over the open
    interval and nowhere else, which is what makes `SR5` and `SR11` pass.
    """

    cid: str
    born: int
    closed: Optional[int] = None

    def open_at(self, t: int) -> bool:
        return t >= self.born and (self.closed is None or t < self.closed)


@dataclass
class World:
    """Opportunity, entitlements and a service budget.

    `opportunity(cid, t) -> [0,1]` is the represented adjudicative opportunity.
    `entitle(cid, t) -> [0,1]` is the service share the policy assigns. A fixture
    revising its service policy does so here, which is how `SR6` is built.
    """

    challenges: tuple
    opportunity: Callable
    entitle: Callable
    horizon: int
    budget: float = BUDGET
    atomic: bool = False

    def live(self, t: int) -> tuple:
        return tuple(c for c in self.challenges if c.open_at(t))

    def opp(self, c: Chal, t: int) -> float:
        return float(self.opportunity(c.cid, t)) if c.open_at(t) else 0.0

    def share(self, c: Chal, t: int) -> float:
        return float(self.entitle(c.cid, t)) if c.open_at(t) else 0.0


def summable_shares(order: Sequence[str], budget: float = BUDGET) -> Callable:
    """`w(c_n) = budget * 2^{-n-1}`, positive and summing below the budget.

    Registration order is used because it is available, **not** because it is the
    right priority rule. The theorem below is parametric in any positive summable
    schedule; this is one witness that such a schedule exists.
    """
    idx = {cid: n for n, cid in enumerate(order)}

    def w(cid, _t):
        n = idx.get(cid)
        return 0.0 if n is None else budget * (0.5 ** (n + 1))
    return w


# ------------------------------------------------------------- schedulers


def serve_positive_share(w: World) -> dict:
    """`u_t(c) = w_t(c) o_t(c)`. Fractional service.

    Budget-feasible whenever `sum_c w_t(c) <= B` and `o_t(c) <= 1`, since then
    `sum_c u_t(c) <= sum_c w_t(c) <= B`.
    """
    out = {}
    for t in range(w.horizon):
        for c in w.live(t):
            out[(c.cid, t)] = w.share(c, t) * w.opp(c, t)
    return out


def serve_least_recently(w: World) -> dict:
    """Atomic: at each position serve one challenge, all of its opportunity.

    Chooses, among live challenges with opportunity **now**, the one served
    longest ago. Adaptivity is the load-bearing part: a fixed cyclic order is
    defeated by adversarial opportunity timing.
    """
    out, last = {}, {}
    for c in w.challenges:
        last[c.cid] = c.born - 1
    for t in range(w.horizon):
        ready = [c for c in w.live(t) if w.opp(c, t) > 0]
        if not ready:
            continue
        pick = min(ready, key=lambda c: (last[c.cid], c.born, c.cid))
        out[(pick.cid, t)] = w.opp(pick, t)
        last[pick.cid] = t
    return out


def serve_fixed_cycle(w: World) -> dict:
    """A non-adaptive dovetailer, kept to exhibit why adaptivity is needed."""
    out = {}
    order = [c.cid for c in w.challenges]
    if not order:
        return out
    for t in range(w.horizon):
        cid = order[t % len(order)]
        c = next((x for x in w.challenges if x.cid == cid), None)
        if c is None or not c.open_at(t):
            continue
        out[(cid, t)] = w.opp(c, t)
    return out


# ------------------------------------------------------------ measurements


def cumulative(series: Mapping, cid: str, upto: int) -> float:
    return sum(v for (k, t), v in series.items() if k == cid and t < upto)


def opportunity_mass(w: World, c: Chal, upto: Optional[int] = None) -> float:
    upto = w.horizon if upto is None else upto
    return sum(w.opp(c, t) for t in range(upto))


def service_mass(w: World, served: Mapping, c: Chal,
                 upto: Optional[int] = None) -> float:
    upto = w.horizon if upto is None else upto
    return cumulative(served, c.cid, upto)


def starvation_debt(w: World, served: Mapping, c: Chal) -> float:
    """`sum_t (o_t - u_t)` over the open interval.

    Reported for comparison with the liability program. It is **not** the
    condition: see `thm_s1_from_positive_share`, where the debt diverges while
    S1 holds.
    """
    return sum(w.opp(c, t) - served.get((c.cid, t), 0.0)
               for t in range(w.horizon) if c.open_at(t))


def budget_violations(w: World, served: Mapping) -> tuple:
    """Positions where total service exceeded the budget, or exceeded the
    opportunity it was serving."""
    bad = []
    for t in range(w.horizon):
        total = sum(served.get((c.cid, t), 0.0) for c in w.challenges)
        if total > w.budget + 1e-9:
            bad.append(("over budget", t, total))
        for c in w.challenges:
            u = served.get((c.cid, t), 0.0)
            if u > w.opp(c, t) + 1e-9:
                bad.append(("served more than the opportunity", t, c.cid))
    return tuple(bad)


# --------------------------------------------------------------- premises


def w1_positive_floor(w: World, eps: float = 1e-12) -> tuple:
    """**W1.** An open undefeated challenge's entitlement has a positive infimum.

    The minimal persistence condition. Not a pinned value: a share may be revised
    downward any number of times and by any finite factor. What it may not do is
    approach zero, which is exactly how a policy revision starves a challenge
    without ever deleting, defeating or formally de-prioritising it.
    """
    bad = []
    for c in w.challenges:
        opens = [t for t in range(w.horizon) if c.open_at(t)]
        if not opens:
            continue
        floor = min(w.share(c, t) for t in opens)
        if floor <= eps:
            bad.append((c.cid, floor))
    return tuple(bad)


def s1_non_starvation(w: World, served: Mapping,
                      unbounded: float = 25.0) -> tuple:
    """**S1**, as the round below stated it, checked on a finite horizon.

    Reports challenges whose opportunity mass exceeded `unbounded` while their
    cumulative service stayed at zero. A finite fixture cannot witness a
    divergence, so this is the honest finite proxy and the document says so.
    """
    bad = []
    for c in w.challenges:
        o = opportunity_mass(w, c)
        u = service_mass(w, served, c)
        if o > unbounded and u <= 0.0:
            bad.append((c.cid, o, u))
    return tuple(bad)


# --------------------------------------------------------------- theorems


def thm_s1_from_positive_share(w: World, served: Mapping) -> dict:
    """**Service Realization, fractional case.**

    Let every open challenge have entitlement bounded below by `w_min(c) > 0`,
    with `sum_c w_t(c) <= B` and `o_t(c) <= 1`. Then `u_t(c) = w_t(c) o_t(c)` is
    budget-feasible and

    ```text
    sum_t u_t(c)  >=  w_min(c) sum_t o_t(c)
    ```

    so unbounded opportunity gives unbounded service. **S1 is derived, not
    assumed.** ∎

    Returns, per challenge, the realized ratio `U/O` against the entitlement
    floor. The ratio must not fall below the floor; that inequality *is* the
    theorem, and it is what a finite fixture can actually check.
    """
    out = {}
    for c in w.challenges:
        opens = [t for t in range(w.horizon) if c.open_at(t)]
        floor = min((w.share(c, t) for t in opens), default=0.0)
        o = opportunity_mass(w, c)
        u = service_mass(w, served, c)
        out[c.cid] = {"floor": floor, "opportunity": o, "service": u,
                      "ratio": (u / o if o > 0 else None),
                      "holds": o <= 0 or u >= floor * o - 1e-9}
    return out


def thm_s1_from_least_recently_served(w: World, served: Mapping) -> dict:
    """**Service Realization, atomic case.**

    With one indivisible service slot per position and an adaptive
    least-recently-served rule, every live challenge with recurring opportunity is
    served infinitely often: a challenge that has waited longest and has
    opportunity now is picked, and only finitely many challenges can be younger
    than it at any moment.

    Returns, per challenge, how many positions it was served and the longest gap
    between consecutive services.
    """
    out = {}
    for c in w.challenges:
        hits = sorted(t for (cid, t) in served if cid == c.cid)
        gaps = [b - a for a, b in zip(hits, hits[1:])]
        out[c.cid] = {"served_at": len(hits),
                      "max_gap": max(gaps) if gaps else None,
                      "opportunity": opportunity_mass(w, c),
                      "service": service_mass(w, served, c)}
    return out


def debt_diverges_while_s1_holds(w: World, served: Mapping) -> dict:
    """The exact reason the liability analogy fails.

    A bounded-exposure theorem would give `D_T` bounded, hence
    `U_T >= O_T - D_T -> infinity`, hence S1. So bounded debt is **sufficient**
    for S1 -- and it is strictly stronger than what the feasible construction
    delivers. Positive-share service leaves `D_T = (1 - w) O_T`, which diverges.

    S1 is a **divergence** condition on service. Liability theorems are
    **boundedness** conditions on exposure. They are not the same shape, and
    nothing here bounds the debt.
    """
    return {c.cid: {"debt": starvation_debt(w, served, c),
                    "opportunity": opportunity_mass(w, c),
                    "service": service_mass(w, served, c)}
            for c in w.challenges}
