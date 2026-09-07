"""Principal-side amendment choice: the argmax-transfer bridge and its settlement target.

`regret_bound` is the finite-menu form of `randomized_approximate_argmax_transfer`
composed with `calibration_through_value_correspondence` (NormativeInductor.lean):
if the displayed values `b` lie within `delta` of an authenticated correspondence point
`w`, `w` lies within `zeta` of the protected values `vplus`, and `pi` is `eta`-optimal
in displayed value, then expected `vplus`-regret ≤ 2·delta + 2·zeta + eta.

`self_referential_gap` is the finite form of the summer negative result: a settlement
target that reads the quote it is scored against (`target(b) = 1[b ≤ 1/2]`) is at
distance ≥ 1/2 from every quote, so `zeta ≥ 1/2` and the bound is vacuous on [0, 1].
"""
from __future__ import annotations

from fractions import Fraction as Q


def expected(pi, v):
    return sum(p * v[q] for q, p in pi.items())


def regret(pi, vplus):
    return max(vplus.values()) - expected(pi, vplus)


def bound_holds(pi, b, w, vplus, delta, zeta, eta):
    """Check the hypotheses, then the conclusion, exactly."""
    qs = list(vplus)
    assert all(abs(w[q] - b[q]) <= delta for q in qs)
    assert all(abs(vplus[q] - w[q]) <= zeta for q in qs)
    best = max(qs, key=lambda q: b[q])
    assert b[best] <= expected(pi, b) + eta
    return regret(pi, vplus) <= 2 * delta + 2 * zeta + eta


def quote_reading_target(bq):
    """H⁺ reads the quote and answers the opposite side of 1/2."""
    return Q(1) if bq <= Q(1, 2) else Q(0)


def self_referential_gap(grid):
    return min(abs(quote_reading_target(b) - b) for b in grid)


def sealed_target(vplus_sealed, bq):
    """A sealed-arm target does not read the quote."""
    return vplus_sealed
