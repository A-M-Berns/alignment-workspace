"""Enforcement: what the market maker's contract does and does not force."""
from __future__ import annotations

import unittest
from fractions import Fraction as F
from itertools import product

from enforcement import (EnforcementTrader, Region, Row, SingleSeparatorTrader,
                         contract_feasible_prices, enforcement_residual, grid)
from market import add, l1, max_gain, min_value

# K = [1/2, 3/4] on one priced sentence.
INTERVAL = Region(1, [Row([F(1)], F(1, 2)), Row([F(-1)], F(-3, 4))])

# K = {p0 >= 1/2, p1 >= 1/2, p0 + p1 <= 3/2} on two.
TRIANGLE = Region(2, [Row([F(1), F(0)], F(1, 2)),
                      Row([F(0), F(1)], F(1, 2)),
                      Row([F(-1), F(-1)], F(-3, 2))])


class ExtremalPinning(unittest.TestCase):
    """The contract is a bound on each coordinate separately."""

    def test_max_gain_decomposes(self):
        p = (F(1, 3), F(3, 4))
        zeta = (F(2), F(-1, 2))
        self.assertEqual(max_gain(zeta, p),
                         F(2) * (1 - F(1, 3)) + F(1, 2) * F(3, 4))

    def test_bound_pins_each_coordinate(self):
        """`max_gain <= eps` forces a bought sentence's price to `1 - eps/xi`."""
        eps = F(1, 8)
        for p0 in (F(i, 8) for i in range(9)):
            for xi in (F(1), F(2), F(5)):
                if max_gain((xi,), (p0,)) <= eps:
                    self.assertLessEqual(1 - p0, eps / xi)

    def test_a_day_strategy_is_worth_nothing_at_its_own_prices(self):
        """No cash term is free: the trade prices out at zero by construction."""
        from market import holdings_value
        p = (F(2, 5), F(7, 10))
        zeta = (F(3), F(-2))
        self.assertEqual(holdings_value(zeta, p, p), 0)


class ExactEnforcement(unittest.TestCase):
    """W1/W4 — at slack zero the contract-feasible set is inside the region."""

    def test_interval_every_intensity(self):
        for beta in (F(1, 100), F(1), F(37)):
            trader = EnforcementTrader(INTERVAL, beta)
            feasible = contract_feasible_prices(trader, 12, F(0))
            self.assertTrue(feasible)
            for p in feasible:
                self.assertTrue(INTERVAL.contains(p), (beta, p))

    def test_intensity_does_not_change_the_feasible_set(self):
        """Exact enforcement is intensity-free; `beta` buys nothing here."""
        sets = [set(contract_feasible_prices(EnforcementTrader(INTERVAL, b), 12,
                                             F(0)))
                for b in (F(1, 100), F(1), F(37))]
        self.assertEqual(sets[0], sets[1])
        self.assertEqual(sets[1], sets[2])

    def test_triangle_two_dimensional(self):
        for beta in (F(1, 10), F(1), F(5)):
            trader = EnforcementTrader(TRIANGLE, beta)
            for p in contract_feasible_prices(trader, 6, F(0)):
                self.assertTrue(TRIANGLE.contains(p), (beta, p))

    def test_the_feasible_set_is_not_empty(self):
        """A vacuous enforcement theorem would also pass the test above."""
        trader = EnforcementTrader(TRIANGLE, F(1))
        self.assertTrue(contract_feasible_prices(trader, 6, F(0)))


class SeparatingPortfolio(unittest.TestCase):
    """W2 — a violation names an actual portfolio, priced and paid for."""

    def test_portfolio_at_a_violating_price(self):
        p = (F(1, 4),)
        trader = EnforcementTrader(INTERVAL, F(2))
        zeta = trader.coefficients(p)
        self.assertEqual(zeta, (F(1, 2),))          # 2 * (1/2 - 1/4) shares
        # what it costs now, what it can pay, what it can lose
        self.assertEqual(max_gain(zeta, p), F(3, 8))
        self.assertEqual(min_value(zeta, p), F(-1, 8))

    def test_gain_when_the_price_violates(self):
        trader = EnforcementTrader(INTERVAL, F(2))
        for p in grid(1, 8):
            zeta = trader.coefficients(p)
            if INTERVAL.contains(p):
                self.assertEqual(zeta, (F(0),))
            else:
                self.assertGreater(max_gain(zeta, p), 0)


class NaiveConstructionFails(unittest.TestCase):
    """W3 — one separating hyperplane enforces one half-space and no more."""

    def test_single_separator_admits_prices_outside_the_region(self):
        naive = SingleSeparatorTrader(INTERVAL, F(1), row_index=0)
        feasible = [p for p in grid(1, 12)
                    if max_gain(naive.coefficients(p), p) <= 0]
        escapes = [p for p in feasible if not INTERVAL.contains(p)]
        self.assertEqual(escapes, [(F(5, 6),), (F(11, 12),), (F(1),)])

    def test_the_full_row_system_closes_them(self):
        trader = EnforcementTrader(INTERVAL, F(1))
        for p in ((F(5, 6),), (F(11, 12),), (F(1),)):
            self.assertGreater(max_gain(trader.coefficients(p), p), 0)


class PositiveSlackBreaksExactness(unittest.TestCase):
    """The algorithm's `2^-n` is not a cosmetic weakening."""

    def test_smallest_escape_under_slack(self):
        trader = EnforcementTrader(INTERVAL, F(1))
        feasible = contract_feasible_prices(trader, 12, F(1, 8))
        escapes = sorted(p for p in feasible if not INTERVAL.contains(p))
        self.assertEqual(escapes, [(F(1, 3),), (F(5, 12),), (F(5, 6),)])

    def test_the_escape_is_exact_arithmetic(self):
        """`p = 1/3` violates `p >= 1/2` by `1/6` and still meets the contract."""
        trader = EnforcementTrader(INTERVAL, F(1))
        p = (F(1, 3),)
        self.assertEqual(INTERVAL.rows[0].violation(p), F(1, 6))
        self.assertEqual(max_gain(trader.coefficients(p), p), F(1, 9))
        self.assertLessEqual(F(1, 9), F(1, 8))


class MasterInequality(unittest.TestCase):
    """`sum_j beta_j g_j(p)^2 <= slack + ordinary volume`, swept exactly."""

    def test_sweep_with_adversarial_ordinary_positions(self):
        trader = EnforcementTrader(TRIANGLE, F(2))
        slack, budget = F(1, 8), F(1, 2)
        axis = [F(i, 4) for i in range(-4, 5)]
        seen = 0
        for p in grid(2, 6):
            for tau in product(axis, repeat=2):
                if l1(tau) > budget:
                    continue
                if max_gain(add(trader.coefficients(p), tau), p) <= slack:
                    seen += 1
                    self.assertGreaterEqual(
                        enforcement_residual(trader, p, slack, budget), 0,
                        (p, tau))
        self.assertGreater(seen, 0)

    def test_ordinary_traders_can_hold_a_violation_open(self):
        """With opposing volume the region is not enforced exactly."""
        trader = EnforcementTrader(INTERVAL, F(1))
        feasible = contract_feasible_prices(trader, 12, F(0), (F(1, 3),))
        self.assertTrue(any(not INTERVAL.contains(p) for p in feasible))


if __name__ == "__main__":
    unittest.main()
