#!/usr/bin/env python3
"""Exact finite geometry for the Service-Value Liability hard pass.

This is not a market simulator.  It checks the finite mixture certificates and
the sharp algebraic closure lemma consumed by the paper proof.  PR50's market
claims remain model-supported claims of PR50, not results of this fixture.
"""

from fractions import Fraction as Q
from typing import Iterable, Sequence


ZERO = Q(0)
ONE = Q(1)


def expectation(weights: Sequence[Q], points: Sequence[Sequence[Q]]) -> tuple[Q, ...]:
    if len(weights) != len(points) or not points:
        raise ValueError("a nonempty point list and one weight per point are required")
    if sum(weights, ZERO) != ONE or any(w < ZERO for w in weights):
        raise ValueError("weights must be a probability distribution")
    width = len(points[0])
    if any(len(p) != width for p in points):
        raise ValueError("point dimensions differ")
    return tuple(sum((w * p[j] for w, p in zip(weights, points)), ZERO)
                 for j in range(width))


def coverage(weights: Sequence[Q]) -> Q:
    return min(weights)


def product_binary(p: Q, q: Q) -> tuple[Q, Q, Q, Q]:
    """Weights on (0,0),(0,1),(1,0),(1,1) with independent means p,q."""
    return ((ONE - p) * (ONE - q), (ONE - p) * q, p * (ONE - q), p * q)


def binary_point_mixture(c: Q) -> tuple[Q, Q]:
    """The unique mixture on settlement values 0,1 with expectation c."""
    if not ZERO <= c <= ONE:
        raise ValueError("binary mean must lie in the unit interval")
    return (ONE - c, c)


def common_mixture_bound(theta: Q, maker_cap: Q = ONE, firm_floor: Q = Q(2)) -> Q:
    """U(1-theta)/theta, where authority value is at most U=C+B_F."""
    if not ZERO < theta <= ONE:
        raise ValueError("coverage must be positive")
    upper = maker_cap + firm_floor
    return upper * (ONE - theta) / theta


def common_mixture_certificate(weights: Sequence[Q], authority_values: Sequence[Q],
                               upper: Q) -> bool:
    """Check the hypotheses and conclusion of the sharp finite algebra lemma."""
    if len(weights) != len(authority_values):
        raise ValueError("one authority value per weight is required")
    if sum(weights, ZERO) != ONE or any(w <= ZERO for w in weights):
        return False
    if any(x > upper for x in authority_values):
        return False
    if sum((w * x for w, x in zip(weights, authority_values)), ZERO) < ZERO:
        return False
    theta = min(weights)
    lower = -upper * (ONE - theta) / theta
    return all(x >= lower for x in authority_values)


def recycling_bound(theta: Q, upper: Q, slack: Q, kappa: Q) -> Q:
    """Closure from Lambda >= -slack-kappa*L and kappa < theta."""
    if not ZERO <= kappa < theta <= ONE:
        raise ValueError("the closure threshold is kappa < theta")
    return (slack + (ONE - theta) * upper) / (theta - kappa)


def repair_gain(direction: Sequence[Q], values: Sequence[Q]) -> Q:
    return sum((u * v for u, v in zip(direction, values)), ZERO)


def in_interval(x: Q, interval: tuple[Q, Q]) -> bool:
    return interval[0] <= x <= interval[1]


def all_positive(values: Iterable[Q]) -> bool:
    return all(x > ZERO for x in values)


# Exact constants from PR50's two-coordinate pump.
PEG = (Q(2, 5), Q(3, 5))
LOW_BAND = (Q(1, 10), Q(1, 5))
HIGH_BAND = (Q(4, 5), Q(9, 10))
ALL4 = ((ZERO, ZERO), (ZERO, ONE), (ONE, ZERO), (ONE, ONE))


def pr50_era_mixture(low: bool) -> tuple[Q, Q, Q, Q]:
    return product_binary(Q(1, 2), Q(3, 20) if low else Q(17, 20))


def pr50_era_mean(low: bool) -> tuple[Q, Q]:
    weights = pr50_era_mixture(low)
    return expectation(weights, ALL4)


if __name__ == "__main__":
    print("centered coverage:", coverage(binary_point_mixture(Q(1, 2))))
    print("near-vertex coverage:", coverage(binary_point_mixture(Q(1, 20))))
    print("PR50 low-era mean:", pr50_era_mean(True))
    print("PR50 high-era mean:", pr50_era_mean(False))
    print("PR50 per-era coverage:", coverage(pr50_era_mixture(True)))
    print("LI common-mixture bound at theta=1/4:", common_mixture_bound(Q(1, 4)))

