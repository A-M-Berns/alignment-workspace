"""Exact enforcement against a declared disturbance class.

The enforcement round's first pass showed the violation-proportional compiler
does not force exact membership once ordinary traders push back. That left open
whether the compiler was weak or exactness impossible. This module settles the
fork, and the answer depends on one property of the region: whether it has an
interior.

The disturbance class is every ordinary aggregate position of `l1` mass at most
`C`. Quantifying over positions rather than over strategies is the strong form:
what matters for contract-feasibility is the realised vector at the displayed
price, so a bound there covers every strategy realising it.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Callable, Sequence

from enforcement import Region, grid
from market import ONE, ZERO, Vector, dot, max_gain

Strategy = Callable[[Sequence[Fraction]], Vector]


def min_max_gain(coefficients: Sequence[Fraction],
                 prices: Sequence[Fraction],
                 budget: Fraction) -> Fraction:
    """The smallest `max_gain` a disturbance of mass `<= budget` can leave.

    `max_gain` is separable over coordinates and convex piecewise-linear in each,
    with its minimum where the coefficient is zero. So the disturbance's best
    play is greedy: spend where a unit of mass buys the largest reduction, which
    is `1 - p` on a long coordinate and `p` on a short one, and stop at zero
    because further spending increases the total again. A brute-force check over
    a disturbance grid agrees exactly — see `test_exactness`.
    """
    base = max_gain(coefficients, prices)
    rates: list[tuple[Fraction, Fraction]] = []
    for xi, p in zip(coefficients, prices):
        if xi > 0:
            rates.append((ONE - p, xi))
        elif xi < 0:
            rates.append((p, -xi))
    rates.sort(key=lambda item: -item[0])
    remaining, saved = Fraction(budget), ZERO
    for rate, amount in rates:
        spend = min(remaining, amount)
        saved += rate * spend
        remaining -= spend
        if remaining == 0:
            break
    return base - saved


def contract_survives(strategy: Strategy,
                      prices: Sequence[Fraction],
                      budget: Fraction,
                      slack: Fraction) -> bool:
    """Whether the market maker could display `prices` against some disturbance."""
    return min_max_gain(strategy(prices), prices, budget) <= Fraction(slack)


def feasible_set(strategy: Strategy, dimension: int, denominator: int,
                 budget: Fraction, slack: Fraction = ZERO) -> list[Vector]:
    return [p for p in grid(dimension, denominator)
            if contract_survives(strategy, p, budget, slack)]


def escapes(strategy: Strategy, region: Region, denominator: int,
            budget: Fraction, slack: Fraction = ZERO) -> list[Vector]:
    """Contract-feasible prices outside the region: the exactness failures."""
    return [p for p in feasible_set(strategy, region.dimension, denominator,
                                    budget, slack)
            if not region.contains(p)]


# --- the interior, which is what decides the fork -------------------------

def strict_interior_point(region: Region, denominator: int) -> Vector | None:
    """A grid point satisfying every row strictly, or `None`.

    Its existence is the hypothesis separating the two halves of the fork. A
    region cut by an equality — every settlement, and every coherence polytope
    over a fragment with a propositional relation — has none.
    """
    for point in grid(region.dimension, denominator):
        if all(row.slack(point) > 0 for row in region.rows) and \
           all(ZERO < x < ONE for x in point):
            return point
    return None


class GaugeTrader:
    """The interior-anchored compiler: a position with a floor outside the region.

    Anchored at a strictly interior point `z`, it holds

        zeta(P) = lam * ramp(gamma(P)) * (z - P),

    where `gamma(P) = max_j (1 - u_j(P))` is the Minkowski gauge of the region
    about `z`, written from the rows as `u_j(P) = (<c_j,P> - r_j)/(<c_j,z> - r_j)`.
    The gauge is one at the boundary and above one outside, so the ramp saturates
    exactly off the region and the position size is bounded below there — which
    is what a disturbance of bounded mass cannot cancel.

    Built from price features, rational constants, addition, multiplication and
    `max`, so it is an expressible feature and a legal trading strategy.

    It is **not** violation-proportional, and it does not vanish on the region:
    inside the collar it holds a position against no violation at all. That is
    exactly what buys exactness, and exactly what costs the safety property of
    `ENFORCEMENT.md` Theorem 2 — see `test_exactness.ExactnessCostsSafety`.
    """

    def __init__(self, region: Region, anchor: Sequence[Fraction],
                 intensity: Fraction, collar: Fraction) -> None:
        if any(row.slack(anchor) <= 0 for row in region.rows):
            raise ValueError("anchor is not strictly interior to the region")
        self.region = region
        self.anchor = tuple(Fraction(x) for x in anchor)
        self.intensity = Fraction(intensity)
        self.collar = Fraction(collar)

    def gauge(self, p: Sequence[Fraction]) -> Fraction:
        return max(ONE - (dot(row.c, p) - row.r) / (dot(row.c, self.anchor) - row.r)
                   for row in self.region.rows)

    def coefficients(self, p: Sequence[Fraction]) -> Vector:
        weight = min(ONE, max(ZERO, (self.gauge(p) - ONE + self.collar) / self.collar))
        return tuple(self.intensity * weight * (z - x)
                     for z, x in zip(self.anchor, p))


# --- the impossibility, for regions without an interior -------------------

def forced_corner_sign(coefficient: Fraction, at_one: bool,
                       budget: Fraction) -> bool:
    """Whether a cube-corner price is ruled out by this coefficient alone.

    At `P_phi = 0` the contract charges nothing for a short position, so a corner
    is excluded only by a long position the disturbance cannot cancel: the
    coefficient must exceed the budget. At `P_phi = 1` the sign reverses. These
    two conditions are what force a continuous one-sentence strategy to change
    sign, and with it to pass through a whole interval on which the disturbance
    can cancel it.
    """
    return (coefficient < -Fraction(budget)) if at_one else (coefficient > Fraction(budget))


def cancellable_interval(slope: Fraction, centre: Fraction,
                         budget: Fraction) -> tuple[Fraction, Fraction]:
    """For the one-sentence strategy `zeta(P) = slope * (centre - P)`, the exact
    interval of prices a disturbance of mass `budget` can cancel.

    Positive width for every finite slope, which is the impossibility: a region
    with no interior cannot contain it.
    """
    if slope <= 0:
        raise ValueError("slope is positive")
    half = Fraction(budget) / slope
    return (centre - half, centre + half)
