"""Traderized realization: projection enforcement, the score identity, the
friction inequality, and the core-minimum misfit bound.

The admissible region is a single rational halfspace `K = { v : <a, v> >= b }`.
That is the case in which every quantity below is exactly rational: the defect
`d = dist(p, K)` and the assessment misfit `e = dist(x, K)` are individually
irrational, but the two quantities the theory actually uses — `d^2` and the
product `d * e` — are not.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence

Vector = Sequence[Fraction]


def dot(u: Vector, v: Vector) -> Fraction:
    return sum((a * b for a, b in zip(u, v)), Fraction(0))


class Halfspace:
    def __init__(self, a: Vector, b: Fraction):
        self.a = list(a)
        self.b = b
        self.norm2 = dot(self.a, self.a)
        if self.norm2 == 0:
            raise ValueError("degenerate halfspace")

    def slack(self, p: Vector) -> Fraction:
        """`max(0, b - <a, p>)` — the unnormalized violation."""
        return max(Fraction(0), self.b - dot(self.a, p))

    def projection(self, p: Vector) -> list[Fraction]:
        s = self.slack(p)
        return [pi + s * ai / self.norm2 for pi, ai in zip(p, self.a)]

    def distance_squared(self, p: Vector) -> Fraction:
        s = self.slack(p)
        return s * s / self.norm2

    def distance_product(self, p: Vector, x: Vector) -> Fraction:
        """`dist(p, K) * dist(x, K)`, which is rational even though neither
        factor is."""
        return self.slack(p) * self.slack(x) / self.norm2


def brier(x: Vector, q: Vector) -> Fraction:
    """`sum_i (q_i - x_i)^2`. For a Boolean truth vector this is the Brier score
    of `q`, and it is the squared Euclidean distance for any `x`."""
    return sum(((qi - xi) ** 2 for qi, xi in zip(q, x)), Fraction(0))


def enforcement_position(region: Halfspace, p: Vector,
                         intensity: Fraction) -> list[Fraction]:
    """`zeta = lambda (proj_K(p) - p)`."""
    q = region.projection(p)
    return [intensity * (qi - pi) for qi, pi in zip(q, p)]


def payoff(zeta: Vector, x: Vector, p: Vector) -> Fraction:
    """The position's value in assessment world `x` at displayed state `p`."""
    return dot(zeta, [xi - pi for xi, pi in zip(x, p)])


def score_identity_gap(region: Halfspace, p: Vector, x: Vector,
                       intensity: Fraction) -> Fraction:
    """`payoff - (lambda/2)(Br_x(p) - Br_x(q) + d^2)`; zero is the identity."""
    q = region.projection(p)
    zeta = enforcement_position(region, p, intensity)
    predicted = intensity * (brier(x, p) - brier(x, q)
                             + region.distance_squared(p)) / 2
    return payoff(zeta, x, p) - predicted


def friction_gap(region: Halfspace, p: Vector, x: Vector,
                 intensity: Fraction) -> Fraction:
    """`payoff - lambda (d^2 - d e)`; nonnegative is the friction inequality."""
    zeta = enforcement_position(region, p, intensity)
    floor = intensity * (region.distance_squared(p)
                         - region.distance_product(p, x))
    return payoff(zeta, x, p) - floor


def core_misfit_bound(region: Halfspace, reference: Vector, vertices: Sequence[Vector],
                      theta: Fraction) -> tuple[bool, Fraction, Fraction]:
    """The core-minimum consequence, in squared form.

    If `q + theta (P - q)` lies inside the endorsed region for every vertex of
    the plausible simplex `P`, then every vertex's misfit obeys
    `e(x)^2 <= (1 - theta)^2 |x - q|^2`, uniformly in how tight the region is.

    Returns `(homothety_holds, worst_misfit_squared, worst_bound)`.
    """
    holds = True
    worst_e2 = Fraction(0)
    worst_bound = Fraction(0)
    for x in vertices:
        shrunk = [qi + theta * (xi - qi) for qi, xi in zip(reference, x)]
        if region.slack(shrunk) > 0:
            holds = False
        e2 = region.distance_squared(x)
        gap = [xi - qi for xi, qi in zip(x, reference)]
        bound = (1 - theta) ** 2 * dot(gap, gap)
        worst_e2 = max(worst_e2, e2)
        worst_bound = max(worst_bound, bound)
    return holds, worst_e2, worst_bound
