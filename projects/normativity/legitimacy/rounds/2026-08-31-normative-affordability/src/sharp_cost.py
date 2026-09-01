"""Persistence under a general date-cost function.

A date's **cost function** `L_t : [0, inf) -> [0, inf)` says what allocating
authority `a` on date `t` charges the liability account in the worst case. Two
instances matter:

    conservative   L_t(a) = q_t sqrt(a) ,          q_t = D_t sqrt(m_t)
    sharp robust   L_t(a) = a s_t^2 / 4            for a <= 4 m_t / s_t^2
                            s_t sqrt(a m_t) - m_t  beyond

with `m_t = eps_t + M_t` and `s_t = D_t` the worst live exclusion depth. Both are
increasing, vanish at zero, and are **star-shaped**: `L_t(a)/a` is nonincreasing.
That is the only structural property the theorems use.

Every fixture stays inside the sharp charge's first branch, where the arithmetic
is rational; the branch boundary is exposed so a caller can check it.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Callable, Sequence

Cost = Callable[[Fraction], Fraction]


# --- the two cost families ------------------------------------------------


def conservative_cost(q: Fraction) -> Cost:
    """`L(a) = q sqrt(a)`, evaluated on perfect squares to stay exact."""
    def cost(a: Fraction) -> Fraction:
        root = _exact_sqrt(a)
        return q * root
    return cost


def conservative_inverse(q: Fraction, budget: Fraction) -> Fraction:
    """`L^{-1}(B) = (B/q)^2`."""
    return (budget / q) ** 2


def sharp_branch_point(s: Fraction, m: Fraction) -> Fraction:
    """`4 m / s^2`, above which the sharp charge leaves its linear branch."""
    return 4 * m / s ** 2


def sharp_cost(s: Fraction, m: Fraction) -> Cost:
    """The exact worst-case charge, on its linear branch.

    Raises above the branch point rather than returning an irrational value, so
    a fixture cannot silently leave the exact regime.
    """
    def cost(a: Fraction) -> Fraction:
        if a > sharp_branch_point(s, m):
            raise ValueError("allocation is past the linear branch")
        return a * s ** 2 / 4
    return cost


def sharp_inverse(s: Fraction, m: Fraction, budget: Fraction) -> Fraction:
    """`L^{-1}(B) = 4B/s^2` while `B <= m`, and `(B+m)^2/(s^2 m)` beyond."""
    if budget <= m:
        return 4 * budget / s ** 2
    return (budget + m) ** 2 / (s ** 2 * m)


def _exact_sqrt(a: Fraction) -> Fraction:
    num, den = a.numerator, a.denominator
    rn, rd = _isqrt(num), _isqrt(den)
    if rn * rn != num or rd * rd != den:
        raise ValueError("square root is irrational; use a perfect square")
    return Fraction(rn, rd)


def _isqrt(n: int) -> int:
    if n < 0:
        raise ValueError("negative")
    x = int(n ** 0.5)
    while x * x > n:
        x -= 1
    while (x + 1) * (x + 1) <= n:
        x += 1
    return x


# --- the criteria ---------------------------------------------------------


def reference_costs(costs: Sequence[Cost],
                    level: Fraction = Fraction(1)) -> list[Fraction]:
    """`L_t(level)` — the sequence whose liminf decides persistence."""
    return [c(level) for c in costs]


def horizon_optimum(inverses: Sequence[Fraction]) -> Fraction:
    """`max_t L_t^{-1}(B)`, the exact finite-horizon cumulative-authority
    optimum: a convex objective on a simplex is maximized at a vertex, so the
    whole budget goes to one date."""
    return max(inverses)


def geometric_schedule(reference: Sequence[Fraction], budget: Fraction,
                       level: Fraction = Fraction(1)) -> list[Fraction]:
    """Allocate `level` on each date whose reference cost fits the next tranche.

    Returns the allocation vector. The charge is at most `budget` and the
    allocated total is `level` times the number of triggers.
    """
    out = [Fraction(0)] * len(reference)
    k = 0
    for t, cost in enumerate(reference):
        tranche = budget / 2 ** (k + 1)
        if cost <= tranche:
            out[t] = level
            k += 1
    return out


def total_charge(costs: Sequence[Cost], alloc: Sequence[Fraction]) -> Fraction:
    return sum((c(a) for c, a in zip(costs, alloc) if a > 0), Fraction(0))


def total_authority(alloc: Sequence[Fraction]) -> Fraction:
    return sum(alloc, Fraction(0))


# --- windows --------------------------------------------------------------


def window_minima(reference: Sequence[Fraction], width: int) -> list[Fraction]:
    """`min_{t in block} L_t(level)`, block by block. The blocks are the cost
    functions of the bounded-delay problem: a minimum of star-shaped costs is
    star-shaped."""
    out = []
    for start in range(0, len(reference), width):
        block = reference[start:start + width]
        if block:
            out.append(min(block))
    return out


# --- the online adversary -------------------------------------------------


def two_date_ratio(commit: Fraction, budget: Fraction,
                   small: Fraction) -> tuple[Fraction, Fraction]:
    """Competitive ratios of committing `commit` at friction 1 on date one.

    Returns `(ratio if the run stops now, ratio if a date of friction `small`
    follows)`. Under the conservative charge, committing `c` at friction `1`
    buys `c^2`, and the remaining `B - c` at friction `small` buys
    `((B-c)/small)^2`.
    """
    if commit > budget:
        raise ValueError("cannot commit more than the budget")
    stop = commit ** 2 / budget ** 2
    rest = budget - commit
    online = commit ** 2 + (rest / small) ** 2
    offline = (budget / small) ** 2
    return stop, online / offline


def cascade_bound(levels: int, delta: Fraction, budget: Fraction,
                  ratio: Fraction) -> Fraction:
    """The budget a rule guaranteeing competitive `ratio` must commit over a
    cascade of `levels` dates with frictions `delta^i`.

    Returns the forced total commitment; exceeding `budget` is the
    contradiction.
    """
    forced = ratio - (levels - 1) * delta ** 2
    if forced <= 0:
        return Fraction(0)
    # each stage must commit at least budget * sqrt(forced); compare squares.
    return Fraction(levels) ** 2 * budget ** 2 * forced


# --- named fixtures -------------------------------------------------------


def review_counterexample(horizon: int) -> dict:
    """`s_t = 1/t`, `m_t = t^4`, so `q_t = t` diverges while `L_t(1) = 1/(4t^2)`
    is summable. Conservatively infeasible, sharply affordable."""
    s = [Fraction(1, t) for t in range(1, horizon + 1)]
    m = [Fraction(t ** 4) for t in range(1, horizon + 1)]
    q = [si * Fraction(_isqrt(mi.numerator)) for si, mi in zip(s, m)]
    costs = [sharp_cost(si, mi) for si, mi in zip(s, m)]
    return {"s": s, "m": m, "q": q, "costs": costs}


def sparse_dips(horizon: int, gap: int) -> list[Fraction]:
    """Reference costs pinned at `1` except at multiples of `gap`, where they
    are `4^-k`."""
    out = []
    k = 0
    for t in range(horizon):
        if t > 0 and t % gap == 0:
            k += 1
            out.append(Fraction(1, 4 ** k))
        else:
            out.append(Fraction(1))
    return out
