"""The exactness fork: when a legal trader can force membership outright."""
from __future__ import annotations

import random
import unittest
from fractions import Fraction as F
from itertools import product

from deduction import support_rows
from enforcement import EnforcementTrader, Region, Row, grid
from exactness import (GaugeTrader, cancellable_interval, contract_survives,
                       escapes, feasible_set, forced_corner_sign, min_max_gain,
                       strict_interior_point)
from market import Fragment, add, holdings_value, l1, max_gain

INTERVAL = Region(1, [Row([F(1)], F(1, 2)), Row([F(-1)], F(-3, 4))])
POINT = Region(1, [Row([F(1)], F(1, 2)), Row([F(-1)], F(-1, 2))])

#: phi and psi mutually exclusive: three plausible worlds, and their convex hull
#: is a triangle — world-inclusive and full-dimensional in the two-cube.
EXCLUSIVE = Fragment(("phi", "psi"), [lambda w: not (w[0] and w[1])])
TRIANGLE = Region(2, [Row([F(1), F(0)], F(0)), Row([F(0), F(1)], F(0)),
                      Row([F(-1), F(-1)], F(-1))])


class DisturbanceOptimum(unittest.TestCase):
    """The greedy is the disturbance's best play, not an approximation to it."""

    def test_agrees_with_brute_force(self):
        random.seed(3)
        axis = [F(i, 12) for i in range(-12, 13)]
        for _ in range(120):
            zeta = tuple(F(random.randint(-8, 8), 4) for _ in range(2))
            price = tuple(F(random.randint(0, 6), 6) for _ in range(2))
            budget = F(random.randint(0, 6), 6)
            brute = min(max_gain(add(zeta, t), price)
                        for t in product(axis, repeat=2) if l1(t) <= budget)
            self.assertEqual(brute, min_max_gain(zeta, price, budget))

    def test_zero_budget_is_the_undisturbed_contract(self):
        self.assertEqual(min_max_gain((F(1, 2),), (F(1, 4),), F(0)),
                         max_gain((F(1, 2),), (F(1, 4),)))


class ViolationProportionalIsNotExact(unittest.TestCase):
    """The first pass's compiler, restated as a fork branch rather than a limit."""

    def test_prices_escape_at_every_intensity(self):
        """Exact arithmetic, not a grid: the escape is `C / beta` below the
        region's lower row, which no finite intensity closes."""
        budget = F(1, 4)
        for beta in (F(8), F(80), F(800), F(10 ** 6)):
            trader = EnforcementTrader(INTERVAL, beta)
            price = (F(1, 2) - budget / beta,)
            self.assertFalse(INTERVAL.contains(price), beta)
            self.assertEqual(trader.coefficients(price), (budget,))
            self.assertTrue(contract_survives(trader.coefficients, price,
                                              budget, F(0)), beta)

    def test_the_escape_shrinks_and_never_closes(self):
        budget = F(1, 4)
        gaps = [budget / beta for beta in (F(8), F(80), F(800))]
        self.assertEqual(gaps, [F(1, 32), F(1, 320), F(1, 3200)])
        self.assertTrue(all(g > 0 for g in gaps))

    def test_a_coarse_grid_reports_no_escape_and_is_wrong(self):
        """Why the fixtures state this one exactly: at high intensity the escape
        is narrower than any grid step, and a grid sweep reads as clean."""
        trader = EnforcementTrader(INTERVAL, F(800))
        self.assertEqual(escapes(trader.coefficients, INTERVAL, 40, F(1, 4)), [])
        price = (F(1, 2) - F(1, 3200),)
        self.assertTrue(contract_survives(trader.coefficients, price, F(1, 4),
                                          F(0)))


class GaugeTraderIsExact(unittest.TestCase):
    """Fork branch A, for a region with an interior."""

    def test_one_sentence(self):
        anchor = (F(5, 8),)
        trader = GaugeTrader(INTERVAL, anchor, F(40), F(1, 4))
        feasible = feasible_set(trader.coefficients, 1, 40, F(1, 4))
        self.assertTrue(feasible)
        for price in feasible:
            self.assertTrue(INTERVAL.contains(price), price)

    def test_two_sentences(self):
        anchor = (F(1, 4), F(1, 4))
        trader = GaugeTrader(TRIANGLE, anchor, F(24), F(1, 2))
        feasible = feasible_set(trader.coefficients, 2, 8, F(1, 8))
        self.assertTrue(feasible)
        for price in feasible:
            self.assertTrue(TRIANGLE.contains(price), price)

    def test_it_refuses_an_anchor_that_is_not_interior(self):
        with self.assertRaises(ValueError):
            GaugeTrader(INTERVAL, (F(1, 2),), F(10), F(1, 4))

    def test_a_region_without_an_interior_admits_no_anchor(self):
        """The construction is unavailable exactly where the impossibility bites."""
        self.assertIsNone(strict_interior_point(POINT, 24))
        self.assertIsNotNone(strict_interior_point(INTERVAL, 24))


class ExactnessCostsSafety(unittest.TestCase):
    """What branch A buys is paid for out of the safety property."""

    def setUp(self):
        self.worlds = EXCLUSIVE.worlds()

    def test_the_region_is_world_inclusive(self):
        for world in self.worlds:
            self.assertTrue(TRIANGLE.contains(world), world)

    def test_violation_proportional_never_loses_in_a_plausible_world(self):
        trader = EnforcementTrader(TRIANGLE, F(4))
        worst = min(holdings_value(trader.coefficients(p), p, w)
                    for p in grid(2, 4) for w in self.worlds)
        self.assertEqual(worst, 0)

    def test_the_gauge_trader_does(self):
        trader = GaugeTrader(TRIANGLE, (F(1, 4), F(1, 4)), F(4), F(1, 2))
        worst = min(holdings_value(trader.coefficients(p), p, w)
                    for p in grid(2, 4) for w in self.worlds)
        self.assertEqual(worst, F(-1, 2))

    def test_the_loss_is_at_a_price_inside_the_region(self):
        """It is not enforcing anything there; it is holding a collar position."""
        trader = GaugeTrader(TRIANGLE, (F(1, 4), F(1, 4)), F(4), F(1, 2))
        price, world = (F(0), F(1, 2)), (F(0), F(1))
        self.assertTrue(TRIANGLE.contains(price))
        self.assertEqual(TRIANGLE.violations(price), (F(0), F(0), F(0)))
        self.assertEqual(holdings_value(trader.coefficients(price), price, world),
                         F(-1, 2))


class ExactnessImpossibleWithoutAnInterior(unittest.TestCase):
    """Fork branch B, by the intermediate-value obstruction."""

    def test_the_corner_conditions_are_forced(self):
        """Exactness at the cube corners forces opposite signs at the two ends."""
        budget = F(1, 8)
        self.assertFalse(forced_corner_sign(F(1, 16), False, budget))
        self.assertTrue(forced_corner_sign(F(1, 4), False, budget))
        self.assertFalse(forced_corner_sign(F(-1, 16), True, budget))
        self.assertTrue(forced_corner_sign(F(-1, 4), True, budget))

    def test_a_cancellable_interval_exists_at_every_slope(self):
        for slope in (F(1), F(40), F(4000)):
            low, high = cancellable_interval(slope, F(1, 2), F(1, 8))
            self.assertLess(low, high)
            for price in ((low,), (high,), (F(1, 2),)):
                self.assertTrue(contract_survives(
                    lambda p, s=slope: (s * (F(1, 2) - p[0]),), price, F(1, 8), F(0)))

    def test_an_explicit_escape_for_a_steep_candidate(self):
        """The grid cannot see it; exact arithmetic can."""
        slope, budget = F(40), F(1, 8)
        price = (F(1, 2) + F(1, 640),)
        self.assertFalse(POINT.contains(price))
        self.assertTrue(contract_survives(
            lambda p: (slope * (F(1, 2) - p[0]),), price, budget, F(0)))

    def test_the_coherence_polytope_has_no_interior(self):
        """Every settlement, and every fragment with a propositional relation,
        lands in branch B."""
        negation = Fragment(("phi", "notphi"), [lambda w: w[0] + w[1] == 1])
        region = Region(2, support_rows(negation, {}))
        self.assertIsNone(strict_interior_point(region, 12))


if __name__ == "__main__":
    unittest.main()
