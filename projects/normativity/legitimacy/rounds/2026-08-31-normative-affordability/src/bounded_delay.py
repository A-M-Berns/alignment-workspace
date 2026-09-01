"""Bounded-delay service: feasibility, minimum cost, and the dual certificate.

Claims `c_t >= 0` arrive at date `t` and must be served within `H` dates. A
transport plan `T(t, s) >= 0` places claim mass, subject to

    sum_s T(t,s) = c_t ,     sum_t T(t,s) <= a_s ,     t <= s <= t + H .

Two different questions, and the round needs both:

- **feasibility** against a *given* service profile `a`, which is what the
  transport conditions of `SERVICE_TRANSFER.md` consume;
- **minimum cost** when `a` is *chosen*, which is what affordability asks.

Date costs are `L_s`, increasing with `L_s(0) = 0` and star-shaped. On the sharp
traderized charge's linear branch `L_s(a) = w_s a` with `w_s = s_s^2/4`, which is
what the fixtures use, so everything is exact.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Callable, Sequence

Cost = Callable[[Fraction], Fraction]


# --- feasibility against a given service profile --------------------------


def interval_condition(claims: Sequence[Fraction], service: Sequence[Fraction],
                       delay: int) -> list[tuple[int, int]]:
    """Every interval `[u,v]` whose claim mass exceeds the capacity of
    `[u, v+H]`. Empty exactly when the plan is feasible."""
    horizon = len(claims)
    bad = []
    for u in range(horizon):
        mass = Fraction(0)
        for v in range(u, horizon):
            mass += claims[v]
            window = service[u:min(v + delay + 1, len(service))]
            if mass > sum(window, Fraction(0)):
                bad.append((u, v))
    return bad


def fifo_misses(claims: Sequence[Fraction], service: Sequence[Fraction],
                delay: int) -> list[int]:
    """Serve oldest first; return the arrival dates whose mass is still
    outstanding when it reaches age `H`.

    FIFO is optimal here: two claims served out of order can always be swapped,
    because the later claim's legal window is contained in the union and both
    dates are legal for both.
    """
    outstanding: list[list] = []          # [arrival, remaining]
    missed = []
    for date in range(len(service)):
        if date < len(claims) and claims[date] > 0:
            outstanding.append([date, claims[date]])
        capacity = service[date]
        while outstanding and capacity > 0:
            arrival, remaining = outstanding[0]
            take = min(capacity, remaining)
            capacity -= take
            outstanding[0][1] -= take
            if outstanding[0][1] == 0:
                outstanding.pop(0)
        expired = [row for row in outstanding if row[0] + delay <= date]
        for row in expired:
            missed.append(row[0])
            outstanding.remove(row)
    for arrival, _ in outstanding:
        missed.append(arrival)
    return sorted(set(missed))


# --- minimum cost when the service profile is chosen ----------------------


def window_minimum(weights: Sequence[Fraction], start: int,
                   delay: int) -> Fraction:
    """`min_{s in [start, start+H]} w_s`, clipped at the horizon."""
    window = weights[start:start + delay + 1]
    if not window:
        raise ValueError("the claim's window falls outside the horizon")
    return min(window)


def min_cost_linear(claims: Sequence[Fraction], weights: Sequence[Fraction],
                    delay: int) -> Fraction:
    """`sum_t c_t min_{s in [t, t+H]} w_s`, the exact optimum for linear costs.

    Each claim independently picks the cheapest date in its own window; nothing
    is gained by batching because a linear cost has no volume discount.
    """
    total = Fraction(0)
    for t, c in enumerate(claims):
        if c == 0:
            continue
        total += c * window_minimum(weights, t, delay)
    return total


def min_cost_dp(claims: Sequence[Fraction], costs: Sequence[Cost],
                delay: int) -> Fraction:
    """Minimum cost over partitions into consecutive runs, each served whole at
    one date legal for all of it.

    Exact when the date costs are star-shaped: no claim gains by splitting its
    mass, and out-of-order service can always be exchanged into runs.
    """
    dates = [t for t, c in enumerate(claims) if c > 0]
    n = len(dates)
    best = [Fraction(0)] + [None] * n
    for j in range(1, n + 1):
        for i in range(j):
            first, last = dates[i], dates[j - 1]
            if last > first + delay:
                continue                       # the run has no common date
            window = range(last, min(first + delay, len(costs) - 1) + 1)
            mass = sum((claims[d] for d in dates[i:j]), Fraction(0))
            run = min((costs[s](mass) for s in window), default=None)
            if run is None:
                continue
            candidate = best[i] + run
            if best[j] is None or candidate < best[j]:
                best[j] = candidate
    return best[n]


def critical_delay(claims: Sequence[Fraction], weights: Sequence[Fraction],
                   budget: Fraction, largest: int) -> int | None:
    """The least `H` whose minimum cost fits the budget; `None` if none does.

    The cost is nonincreasing in `H` — a wider window is a superset — so the
    affordable delays form an up-set and the least one is well defined.
    """
    for delay in range(0, largest + 1):
        try:
            if min_cost_linear(claims, weights, delay) <= budget:
                return delay
        except ValueError:
            continue
    return None


# --- the dual certificate -------------------------------------------------


def cap_cost(costs: Sequence[Cost], window: Sequence[int],
             mass: Fraction) -> Fraction:
    """`min { sum_{s in J} L_s(a_s) : sum a_s >= mass } = min_{s in J} L_s(mass)`.

    Star-shapedness: `L_s(a_s) >= (a_s/mass) L_s(mass) >= (a_s/mass) min_j`,
    and summing recovers the minimum.
    """
    return min(costs[s](mass) for s in window)


def deadline_certificate(claims: Sequence[Fraction], costs: Sequence[Cost],
                         delay: int, intervals: Sequence[tuple[int, int]],
                         budget: Fraction) -> tuple[bool, Fraction]:
    """Check a packing of claim intervals with pairwise disjoint neighbourhoods.

    Returns `(certifies, total)`. A total above the budget proves that no
    bounded-delay plan fits, because each interval's mass must be carried inside
    its own neighbourhood and the neighbourhoods do not share a date.
    """
    seen: set[int] = set()
    total = Fraction(0)
    for u, v in intervals:
        window = list(range(u, min(v + delay, len(costs) - 1) + 1))
        if seen.intersection(window):
            raise ValueError("the neighbourhoods overlap; the bound is unsound")
        seen.update(window)
        mass = sum(claims[u:v + 1], Fraction(0))
        total += cap_cost(costs, window, mass)
    return total > budget, total


# --- the online dilemma ---------------------------------------------------


def two_date_service(first: Fraction, second: Fraction,
                     commit: Fraction) -> tuple[Fraction, Fraction]:
    """One unit claim, legal dates one and two, linear costs.

    `commit` is the fraction served at the first date, chosen before the second
    date's cost is known. Returns `(online cost, offline cost)`.
    """
    if not 0 <= commit <= 1:
        raise ValueError("the committed fraction is between zero and one")
    online = commit * first + (1 - commit) * second
    offline = min(first, second)
    return online, offline


# --- named fixtures -------------------------------------------------------


def linear_costs(weights: Sequence[Fraction]) -> list[Cost]:
    return [(lambda a, w=w: w * a) for w in weights]


def dip_weights(horizon: int, gap: int) -> list[Fraction]:
    """Date weights pinned at `1` except at multiples of `gap`, where they are
    `4^-k`. Unconstrained persistence holds; bounded delay may not."""
    out = []
    k = 0
    for t in range(horizon):
        if t > 0 and t % gap == 0:
            k += 1
            out.append(Fraction(1, 4 ** k))
        else:
            out.append(Fraction(1))
    return out
