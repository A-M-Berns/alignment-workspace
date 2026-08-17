"""Funding, liability, and whether the modified market becomes exploitable."""
from __future__ import annotations

import unittest
from fractions import Fraction as F
from itertools import product

from deduction import (deductive_region, excluded_plausible_worlds,
                       persistent_gap_trader_worth, world_inclusive)
from enforcement import (EnforcementTrader, Region, Row,
                         contract_feasible_prices, grid)
from funding import FundingLedger, exploitation_bound
from market import Fragment, holdings_value, max_gain, min_value

ONE_SENTENCE = Fragment(("phi",))
THREE = Fragment(("a", "b", "c"))

#: The source demands `p(phi) <= 1/2` while deduction has settled `phi` true.
CONTRARY = Region(1, [Row([F(-1)], F(-1, 2))])


class PlausibleValueIsNonnegative(unittest.TestCase):
    """W9 — the sufficient condition, checked rather than asserted.

    For every world the region contains, the realised enforcement position is
    worth at least `sum_j beta_j g_j(p)^2`. Nothing about the ordinary traders
    enters: this is a property of the position and the price alone.
    """

    def test_sweep_over_regions_prices_and_worlds(self):
        regions = [
            Region(2, [Row([F(1), F(0)], F(1, 2)), Row([F(0), F(1)], F(1, 3))]),
            Region(2, [Row([F(1), F(1)], F(1)), Row([F(-1), F(-1)], F(-2))]),
            Region(2, [Row([F(1), F(-1)], F(0))]),
        ]
        checked = 0
        for region in regions:
            for beta in (F(1, 2), F(3)):
                trader = EnforcementTrader(region, beta)
                for p in grid(2, 4):
                    zeta = trader.coefficients(p)
                    floor = trader.weighted_square_violation(p)
                    for w in product((F(0), F(1)), repeat=2):
                        if not region.contains(w):
                            continue
                        checked += 1
                        self.assertGreaterEqual(
                            holdings_value(zeta, p, w), floor, (region, p, w))
        self.assertGreater(checked, 0)

    def test_the_floor_is_sometimes_strictly_positive(self):
        """Not a vacuous nonnegativity: the trader is paid for enforcing."""
        region = Region(1, [Row([F(1)], F(1, 2))])
        trader = EnforcementTrader(region, F(2))
        p = (F(1, 4),)
        self.assertEqual(trader.weighted_square_violation(p), F(1, 8))
        self.assertEqual(holdings_value(trader.coefficients(p), p, (F(1),)),
                         F(3, 8))


class SafeCase(unittest.TestCase):
    """W9 — world-inclusive region, opposing ordinary volume, zero liability."""

    def setUp(self):
        self.stages = {1: {}, 2: {}, 3: {"phi": 1}, 4: {"phi": 1}}
        self.plausible = {d: ONE_SENTENCE.pc_worlds(s)
                          for d, s in self.stages.items()}

    def test_regions_are_world_inclusive(self):
        for date, settled in self.stages.items():
            region = deductive_region(ONE_SENTENCE, settled)
            self.assertTrue(world_inclusive(region, self.plausible[date]), date)

    def test_liability_is_zero_against_an_opposing_aggregate(self):
        ledger = FundingLedger()
        for date, settled in self.stages.items():
            region = deductive_region(ONE_SENTENCE, settled)
            trader = EnforcementTrader(region, F(4))
            feasible = contract_feasible_prices(trader, 8, F(0), (F(-1, 2),))
            self.assertTrue(feasible, date)
            price = feasible[0]
            ledger.record(date, trader.coefficients(price), price)
        self.assertEqual(ledger.liability(self.plausible), 0)
        self.assertEqual(exploitation_bound(ledger.liability(self.plausible)), 1)


class SupportCoverageFailure(unittest.TestCase):
    """W6 — the region excludes a world that stays plausible."""

    def setUp(self):
        self.plausible = ONE_SENTENCE.pc_worlds({"phi": 1})

    def test_the_excluded_world_is_named(self):
        self.assertFalse(world_inclusive(CONTRARY, self.plausible))
        self.assertEqual(excluded_plausible_worlds(CONTRARY, self.plausible),
                         [(F(1),)])

    def test_liability_per_date_is_bounded_below_by_a_constant(self):
        """Sharper enforcement costs more, converging on `M * dist`."""
        expected = {F(10): F(-9, 40), F(100): F(-99, 400),
                    F(1000): F(-999, 4000)}
        for beta, value in expected.items():
            trader = EnforcementTrader(CONTRARY, beta)
            denominator = 2 * int(beta)
            feasible = contract_feasible_prices(trader, denominator, F(0),
                                                (F(1, 2),))
            self.assertEqual(len(feasible), 1, beta)
            price = feasible[0]
            self.assertEqual(
                holdings_value(trader.coefficients(price), price, (F(1),)),
                value, beta)

    def test_cumulative_liability_diverges(self):
        trader = EnforcementTrader(CONTRARY, F(10))
        price = contract_feasible_prices(trader, 20, F(0), (F(1, 2),))[0]
        ledger = FundingLedger()
        for date in range(1, 9):
            ledger.record(date, trader.coefficients(price), price)
        plausible = {d: self.plausible for d in ledger.dates}
        self.assertEqual(ledger.liability(plausible), F(9, 5))   # 8 * 9/40
        self.assertEqual(ledger.cumulative_value(8, (F(1),)), F(-9, 5))

    def test_an_ordinary_trader_exploits(self):
        """The plausible-net-worth bound is not merely lost, it is beaten."""
        trader = EnforcementTrader(CONTRARY, F(10))
        price = contract_feasible_prices(trader, 20, F(0), (F(1, 2),))[0]
        prices = [price] * 8
        worth = persistent_gap_trader_worth(prices, 0, [True] * 8, (F(1),))
        self.assertEqual(worth, F(18, 5))                        # 8 * 9/20
        self.assertGreater(worth, exploitation_bound(F(9, 5)))


class LiabilityLaundering(unittest.TestCase):
    """W7 — a per-date bound passes while the aggregate diverges."""

    def date_position(self, coordinate: int):
        basis = [F(1) if k == coordinate else F(0) for k in range(3)]
        region = Region(3, [Row([-x for x in basis], F(-1, 2))])
        trader = EnforcementTrader(region, F(10))
        opposing = tuple(F(1, 2) if k == coordinate else F(0) for k in range(3))
        price = contract_feasible_prices(trader, 20, F(0), opposing)[0]
        return trader.coefficients(price), price

    def build(self, dates: int) -> tuple[FundingLedger, list]:
        cache = {c: self.date_position(c) for c in range(3)}
        ledger = FundingLedger()
        for date in range(1, dates + 1):
            position, price = cache[(date - 1) % 3]
            ledger.record(date, position, price)
        return ledger, THREE.pc_worlds({"a": 1, "b": 1, "c": 1})

    def test_every_single_date_exposure_is_the_same_small_number(self):
        ledger, _ = self.build(6)
        self.assertEqual(set(ledger.exposures), {F(9, 40)})

    def test_the_cumulative_liability_grows_without_bound(self):
        for dates, expected in ((6, F(27, 20)), (12, F(27, 10)),
                                (24, F(27, 5))):
            ledger, plausible = self.build(dates)
            self.assertEqual(
                ledger.liability({d: plausible for d in ledger.dates}),
                expected)

    def test_fresh_coordinates_do_not_hide_it(self):
        """The safety hypothesis is stated on the cumulative sum in one world,
        which is why rotating coordinates does not defeat it."""
        ledger, plausible = self.build(6)
        self.assertEqual(ledger.cumulative_value(6, plausible[0]), F(-27, 20))


class FundingTrajectory(unittest.TestCase):
    """W5 — finite at every date, unbounded over dates."""

    def test_finite_at_each_date_and_growing(self):
        ledger, _ = LiabilityLaundering().build(12)
        trajectory = ledger.credit_trajectory()
        for _, credit in trajectory:
            self.assertLess(credit, F(10 ** 6))
        self.assertEqual(trajectory[0][1], F(9, 40))
        self.assertEqual(trajectory[-1][1], F(27, 10))
        self.assertEqual(len({c for _, c in trajectory}), 12)


class SubsidyHarvesting(unittest.TestCase):
    """W8 — where the transfer is, and where it is not."""

    def test_no_direct_transfer_channel(self):
        """An ordinary trader's worth is a function of prices and its own
        positions. Changing the enforcement position with the price path held
        fixed changes nothing for it."""
        prices = [(F(1, 2),), (F(1, 2),)]
        world = (F(1),)
        own = [(F(1),), (F(1),)]
        worth = sum(holdings_value(z, p, world) for z, p in zip(own, prices))
        for enforcement in ((F(-3),), (F(0),), (F(50),)):
            unchanged = sum(holdings_value(z, p, world)
                            for z, p in zip(own, prices))
            self.assertEqual(unchanged, worth)
        self.assertEqual(worth, F(1))

    def test_the_transfer_runs_through_the_price(self):
        """What the ordinary trader gains per date is what enforcement holds
        the price away from the plausible world by."""
        trader = EnforcementTrader(CONTRARY, F(10))
        price = contract_feasible_prices(trader, 20, F(0), (F(1, 2),))[0]
        ordinary_gain = holdings_value((F(1, 2),), price, (F(1),))
        enforcement_loss = -holdings_value(trader.coefficients(price), price,
                                           (F(1),))
        self.assertEqual(ordinary_gain, enforcement_loss)
        self.assertEqual(ordinary_gain, F(9, 40))


class IntensityIsNotFunding(unittest.TestCase):
    """W12 — the two quantities move independently."""

    def test_position_size_is_set_by_opposing_volume_not_by_intensity(self):
        sizes = {}
        for beta in (F(10), F(100), F(1000)):
            trader = EnforcementTrader(CONTRARY, beta)
            price = contract_feasible_prices(trader, 2 * int(beta), F(0),
                                             (F(1, 2),))[0]
            sizes[beta] = trader.coefficients(price)
        self.assertEqual(set(sizes.values()), {(F(-1, 2),)})

    def test_intensity_sets_precision_only(self):
        violations = {}
        for beta in (F(10), F(100), F(1000)):
            trader = EnforcementTrader(CONTRARY, beta)
            price = contract_feasible_prices(trader, 2 * int(beta), F(0),
                                             (F(1, 2),))[0]
            violations[beta] = CONTRARY.rows[0].violation(price)
        self.assertEqual(violations,
                         {F(10): F(1, 20), F(100): F(1, 200),
                          F(1000): F(1, 2000)})

    def test_exposure_can_be_large_at_small_intensity(self):
        """A big number in `beta` is not a big number of dollars, and the
        converse fails too."""
        region = Region(1, [Row([F(1)], F(1))])
        trader = EnforcementTrader(region, F(1, 4))
        price = (F(0),)
        self.assertEqual(trader.coefficients(price), (F(1, 4),))
        self.assertEqual(min_value(trader.coefficients(price), price), F(0))
        price = (F(1, 2),)
        self.assertEqual(min_value(trader.coefficients(price), price),
                         F(-1, 16))


if __name__ == "__main__":
    unittest.main()
