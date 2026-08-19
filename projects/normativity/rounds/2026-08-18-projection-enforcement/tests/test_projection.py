"""Exact-arithmetic regression tests for the projection enforcement trader.

Every assertion is over `Fraction`s.  The Lean files carry the theorems; these
tests exist to catch a transcription error between the algebra and the paper, to
exhibit the comparison against the row construction on displayed data, and to
mirror the two negative results.
"""

from __future__ import annotations

import itertools
import os
import sys
import unittest
from fractions import Fraction as F

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "src"))

import projection as P  # noqa: E402


SIMPLEX = [[F(0), F(0)], [F(1), F(0)], [F(0), F(1)]]
SQUARE = [[F(0), F(0)], [F(1), F(0)], [F(0), F(1)], [F(1), F(1)]]
SEGMENT = [[F(0), F(0)], [F(1), F(1)]]

POINTS = [
    [F(1), F(1)],
    [F(1, 2), F(1, 2)],
    [F(-3), F(2)],
    [F(1, 4), F(7, 8)],
    [F(5, 3), F(-1, 3)],
    [F(0), F(0)],
]


def barycentric_grid(V, denom):
    """Rational points of `conv(V)` with barycentric weights over `denom`."""
    k = len(V)
    dim = len(V[0])
    out = []
    for cut in itertools.combinations(range(denom + k - 1), k - 1):
        prev = -1
        weights = []
        for c in cut:
            weights.append(c - prev - 1)
            prev = c
        weights.append(denom + k - 2 - prev)
        lam = [F(w, denom) for w in weights]
        out.append([sum((lam[i] * V[i][j] for i in range(k)), F(0))
                    for j in range(dim)])
    return out


class TestProjectionIsCorrect(unittest.TestCase):
    def test_variational_inequality_certifies_every_case(self):
        for V in (SIMPLEX, SQUARE, SEGMENT):
            for p in POINTS:
                q = P.project(p, V)
                self.assertTrue(P.satisfies_vi(p, q, V))

    def test_no_grid_point_is_closer(self):
        for V in (SIMPLEX, SQUARE, SEGMENT):
            for p in POINTS:
                q = P.project(p, V)
                best = P.sq_dist(p, q)
                for y in barycentric_grid(V, 12):
                    self.assertLessEqual(best, P.sq_dist(p, y))

    def test_projection_fixes_admitted_points(self):
        for V in (SIMPLEX, SQUARE, SEGMENT):
            for y in barycentric_grid(V, 6):
                self.assertEqual(P.project(y, V), list(y))


class TestForceInequalities(unittest.TestCase):
    """The three inequalities `ProjectionForce` proves, on displayed data."""

    def test_force_inequality(self):
        # lam * ||q - p||^2 <= <zeta, y - p>  for every admitted y.
        for V in (SIMPLEX, SQUARE, SEGMENT):
            for p in POINTS:
                for lam in (F(1), F(3, 2), F(17, 5)):
                    q = P.project(p, V)
                    zeta = P.shares(lam, p, q)
                    lhs = lam * P.sq_dist(p, q)
                    for y in barycentric_grid(V, 8):
                        self.assertLessEqual(lhs, P.trade_value(zeta, p, y))

    def test_value_nonnegative_at_admitted_points(self):
        for V in (SIMPLEX, SQUARE, SEGMENT):
            for p in POINTS:
                q = P.project(p, V)
                zeta = P.shares(F(2), p, q)
                for y in barycentric_grid(V, 8):
                    self.assertGreaterEqual(P.trade_value(zeta, p, y), 0)

    def test_liability_is_calibrated(self):
        # lam * (||q-p||^2 - ||q-p||*||z-w||) <= <zeta, w - p>, checked by
        # squaring so that no square root is ever taken.
        for V in (SIMPLEX, SQUARE, SEGMENT):
            for p in POINTS:
                q = P.project(p, V)
                lam = F(5, 2)
                zeta = P.shares(lam, p, q)
                A = P.sq_dist(p, q)
                for w in POINTS:
                    z = P.project(w, V)
                    B = P.sq_dist(w, z)
                    val = P.trade_value(zeta, p, w) / lam
                    gap = A - val
                    if gap > 0:
                        self.assertLessEqual(gap * gap, A * B)

    def test_intensity_buys_the_tolerance(self):
        # The algebraic step: lam*||q-p||^2 <= rho and lam >= rho/delta^2
        # give ||q-p|| <= delta.  Checked squared.
        for rho in (F(1, 8), F(1), F(9, 4)):
            for delta in (F(1, 2), F(1, 10), F(3)):
                lam = rho / (delta * delta)
                sq = rho / lam
                self.assertLessEqual(sq, delta * delta)


class TestSupNormFollows(unittest.TestCase):
    """The paper's l-infinity conclusion is implied with the same tolerance."""

    def test_sup_distance_never_exceeds_euclidean(self):
        for V in (SIMPLEX, SQUARE, SEGMENT):
            for p in POINTS:
                q = P.project(p, V)
                s = P.sup_dist(p, q)
                self.assertLessEqual(s * s, P.sq_dist(p, q))


class TestRowsAreTheSpecialCase(unittest.TestCase):
    """One halfspace: the row position and the projection position coincide."""

    def test_single_halfspace_positions_agree(self):
        # K = {x : <c, x> >= r}.  proj(p) = p + g(p) * c / ||c||^2, so the
        # projection position at intensity lam is the row position at
        # beta = lam / ||c||^2.
        cases = [
            ([F(1), F(0)], F(1, 2), [F(0), F(0)]),
            ([F(1), F(1)], F(1), [F(0), F(0)]),
            ([F(2), F(-1)], F(1), [F(1, 4), F(3, 4)]),
        ]
        for c, r, p in cases:
            nc = P.dot(c, c)
            g = P.row_violation(c, r, p)
            lam = F(3)
            beta = lam / nc
            proj_pos = [lam * g * ci / nc for ci in c]
            row_pos = P.row_shares([(c, r, beta)], p)
            self.assertEqual(proj_pos, row_pos)


class TestPresentationDependence(unittest.TestCase):
    """Section 9.1's claim, on exact data: no presentation-independent constant
    turns a small maximal row violation into a small distance."""

    def test_rescaled_rows_shrink_the_violation_without_moving_the_region(self):
        V = SIMPLEX
        p = [F(1), F(1)]
        true_sq = P.sq_dist(p, P.project(p, V))
        self.assertEqual(true_sq, F(1, 2))
        base = [
            ([F(1), F(0)], F(0)),
            ([F(0), F(1)], F(0)),
            ([F(-1), F(-1)], F(-1)),
        ]
        previous = None
        for N in (1, 10, 100, 1000):
            rows = [([ci / N for ci in c], r / N, F(1)) for c, r in base]
            viol = P.max_row_violation(rows, p)
            self.assertEqual(viol, F(1, N))
            if previous is not None:
                self.assertLess(viol, previous)
            previous = viol
        # The Euclidean distance is unchanged by any of it.
        self.assertEqual(true_sq, P.sq_dist(p, P.project(p, V)))

    def test_projection_intensity_is_presentation_free(self):
        # The row route needs beta >= rho * N^2 / delta^2 under the 1/N
        # rescaling; the projection route needs lam >= rho / delta^2 always.
        rho, delta = F(1), F(1, 4)
        lam = rho / (delta * delta)
        for N in (1, 10, 100):
            c = [F(1, N), F(0)]
            beta_needed = rho / (delta * delta * P.dot(c, c))
            self.assertEqual(beta_needed, lam * N * N)


class TestLateAdmissionCounterexample(unittest.TestCase):
    """The numeric mirror of `late_admission_is_not_enough`: admission at the
    final date does not bound the cumulative value."""

    def test_cumulative_value_is_negative(self):
        p0 = [F(1, 2)]
        region0 = [[F(0)]]
        q0 = P.project(p0, region0)
        self.assertEqual(q0, [F(0)])
        zeta0 = P.shares(F(1), p0, q0)
        self.assertEqual(zeta0, [F(-1, 2)])
        w = [F(1)]
        day0 = P.trade_value(zeta0, p0, w)
        # Day 1 admits everything, so its projection is the price and the
        # position is empty.
        p1 = [F(1, 2)]
        region1 = [[F(0)], [F(1)]]
        q1 = P.project(p1, region1)
        self.assertEqual(q1, p1)
        day1 = P.trade_value(P.shares(F(0), p1, q1), p1, w)
        self.assertEqual(day1, 0)
        self.assertEqual(day0 + day1, F(-1, 4))
        # w is admitted by the final region and the cumulative value is
        # still negative.
        self.assertTrue(any(v == w for v in region1))
        self.assertLess(day0 + day1, 0)


if __name__ == "__main__":
    unittest.main()
