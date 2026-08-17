"""The force contract, and safety below world-inclusiveness."""
from __future__ import annotations

import unittest
from fractions import Fraction as F

from contract import (ForceDeclaration, certified_intensity,
                      cumulative_liability_bound, volume_times_depth)
from deduction import (incoherence_upper, net_rows, world_deficit,
                       world_inclusive)
from enforcement import EnforcementTrader, Region, Row, grid
from funding import FundingLedger, exploitation_bound
from market import Fragment, holdings_value

WORLD = (F(1),)          #: the one world still plausible once `phi` is settled


def reserving_region(depth: F) -> Region:
    """`K = {P <= 1 - depth}`: a source reserving against full certainty."""
    return Region(1, [Row([F(-1)], -(F(1) - depth))])


class Declaration(unittest.TestCase):
    """What the mechanism signs, and that the promise follows from it."""

    def test_intensity_buys_the_promised_tolerance(self):
        region = reserving_region(F(1, 2))
        for tolerance in (F(1, 4), F(1, 10), F(1, 100)):
            declaration = ForceDeclaration(region, F(3), F(1, 8), tolerance)
            self.assertEqual(declaration.intensity,
                             (F(1, 8) + F(3)) / tolerance ** 2)

    def test_conformance_follows_from_the_budget(self):
        """Any price consuming at most `slack + volume` meets the promise."""
        region = reserving_region(F(1, 2))
        declaration = ForceDeclaration(region, F(3), F(1, 8), F(1, 10))
        for price in grid(1, 60):
            if declaration.budget_consumed(price) <= F(1, 8) + F(3):
                self.assertTrue(declaration.conformance_holds(price), price)

    def test_a_zero_tolerance_is_refused(self):
        with self.assertRaises(ValueError):
            certified_intensity(F(1, 8), F(3), F(0))


class LiabilityCeiling(unittest.TestCase):
    """Intensity cancels: the ceiling is volume times exclusion depth."""

    def test_the_bound_is_intensity_free_at_equilibrium(self):
        depth, volume, slack = F(1, 4), F(2), F(1, 16)
        region = reserving_region(depth)
        for tolerance in (F(1, 5), F(1, 20), F(1, 200)):
            declaration = ForceDeclaration(region, volume, slack, tolerance)
            violation = volume / declaration.intensity
            price = (F(1) - depth + violation,)
            self.assertTrue(declaration.conformance_holds(price))
            self.assertEqual(declaration.liability_bound(price, WORLD),
                             volume * depth)

    def test_it_matches_the_volume_times_depth_reading(self):
        region = reserving_region(F(1, 4))
        self.assertEqual(volume_times_depth(F(2), world_deficit(region, WORLD)),
                         F(1, 2))

    def test_a_world_inclusive_region_has_depth_zero(self):
        region = Region(1, [Row([F(1)], F(0))])
        self.assertTrue(world_inclusive(region, [WORLD]))
        self.assertEqual(world_deficit(region, WORLD), (F(0),))
        self.assertEqual(volume_times_depth(F(1000), world_deficit(region, WORLD)),
                         F(0))


class SafeWithoutWorldInclusiveness(unittest.TestCase):
    """A region that excludes a live world at every date, enforced forever,
    with bounded cumulative enforcement liability."""

    DATES = 14

    def trajectory(self):
        ledger, schedule = FundingLedger(), []
        for n in range(1, self.DATES + 1):
            depth, volume, slack = F(1, 2 ** n), F(n), F(1, 2 ** (n + 1))
            region = reserving_region(depth)
            declaration = ForceDeclaration(region, volume, slack, F(1, 10))
            violation = volume / declaration.intensity
            price = (F(1) - depth + violation,)
            assert declaration.conformance_holds(price)
            ledger.record(n, declaration.trader().coefficients(price), price)
            schedule.append((volume, world_deficit(region, WORLD)))
        return ledger, schedule

    def test_no_date_is_world_inclusive(self):
        for n in range(1, self.DATES + 1):
            region = reserving_region(F(1, 2 ** n))
            self.assertFalse(world_inclusive(region, [WORLD]), n)

    def test_conformance_holds_at_every_date(self):
        self.trajectory()          # the assertion is inside

    def test_cumulative_liability_stays_under_its_bound(self):
        ledger, schedule = self.trajectory()
        realised = ledger.liability({d: [WORLD] for d in ledger.dates})
        bound = cumulative_liability_bound(schedule)
        self.assertLessEqual(realised, bound)
        # sum_{n=1}^{N} n / 2^n  =  2 - (N + 2) / 2^N
        self.assertEqual(bound, F(2) - F(self.DATES + 2, 2 ** self.DATES))

    def test_the_bound_converges(self):
        """`sum_n n / 2^n = 2`, so the criterion survives at every horizon."""
        _, schedule = self.trajectory()
        self.assertLess(cumulative_liability_bound(schedule), F(2))
        self.assertLess(exploitation_bound(cumulative_liability_bound(schedule)),
                        F(3))

    def test_the_liability_is_real_not_an_artefact(self):
        """Every date does show a plausible loss; the sum is what converges."""
        ledger, _ = self.trajectory()
        for date in ledger.dates:
            self.assertLess(ledger.cumulative_value(date, WORLD), 0)


class UnsafeWhenDepthDoesNotDecay(unittest.TestCase):
    """The contrast case: fixed depth, growing volume, divergent bound."""

    def test_the_bound_grows_without_limit(self):
        schedule = [(F(n), (F(1, 2),)) for n in range(1, 21)]
        partial = [cumulative_liability_bound(schedule[:k]) for k in (5, 10, 20)]
        self.assertEqual(partial, [F(15, 2), F(55, 2), F(105)])
        self.assertLess(partial[0], partial[1])
        self.assertLess(partial[1], partial[2])


class ConstrainedMakerNeedsAnExistenceTheorem(unittest.TestCase):
    """The asymmetry between the two implementations of the force contract.

    Logical Induction's market maker is total: a fixed point exists for whatever
    aggregate it is handed. A market maker additionally required to display a
    price inside the region must satisfy two demands at once, and nothing
    supplies a joint solution — here there is none.
    """

    REGION = Region(1, [Row([F(-1)], F(-1, 2))])          # K = {P <= 1/2}
    ORDINARY = (F(1),)                                    # buys one share, flat

    def contract_holds(self, price, coefficients):
        from market import max_gain
        return max_gain(coefficients, price) <= 0

    def test_no_price_satisfies_both_demands(self):
        joint = [p for p in grid(1, 40)
                 if self.REGION.contains(p)
                 and self.contract_holds(p, self.ORDINARY)]
        self.assertEqual(joint, [])

    def test_the_contract_alone_is_satisfiable(self):
        alone = [p for p in grid(1, 40) if self.contract_holds(p, self.ORDINARY)]
        self.assertEqual(alone, [(F(1),)])

    def test_the_region_alone_is_nonempty(self):
        self.assertTrue([p for p in grid(1, 40) if self.REGION.contains(p)])

    def test_traderizing_keeps_a_solution_and_declares_its_tolerance(self):
        """Changing the aggregate leaves the market maker total. What the
        enforcement trader then owes is conformance, not membership."""
        for beta, gap in ((F(8), F(1, 8)), (F(80), F(1, 80))):
            trader = EnforcementTrader(self.REGION, beta)
            price = (F(1, 2) + gap,)
            self.assertTrue(self.contract_holds(
                price, tuple(a + b for a, b in
                             zip(trader.coefficients(price), self.ORDINARY))))
            self.assertEqual(self.REGION.violations(price), (gap,))


class IncoherenceBridge(unittest.TestCase):
    """Row violations against the quantity the settlement interface measures."""

    #: `NL-SI-C5`'s instance: `A` at `{w1,w2}`, `B` at `{w2,w3}`, `C` at `{w2}`.
    WORLDS = [(F(1), F(0), F(0)), (F(1), F(1), F(1)), (F(0), F(1), F(0))]
    PRICE = (F(9, 10), F(9, 10), F(0))

    def test_the_interfaces_number_is_recovered_independently(self):
        self.assertEqual(incoherence_upper(self.PRICE, self.WORLDS, 30), F(4, 15))

    def test_a_fine_enough_net_sees_all_of_it(self):
        rows = net_rows(self.WORLDS, 3, 3)
        self.assertEqual(max(row.violation(self.PRICE) for row in rows), F(4, 15))

    def test_a_coarse_net_sees_none_of_it(self):
        """The presentation's resolution is what decides how much incoherence
        enforcement can respond to — the tight certificate has mass `1/3` per
        coordinate and a coarser net cannot express it."""
        for denominator in (1, 2):
            rows = net_rows(self.WORLDS, 3, denominator)
            self.assertEqual(max(row.violation(self.PRICE) for row in rows), F(0))

    def test_net_rows_are_world_inclusive(self):
        rows = net_rows(self.WORLDS, 3, 3)
        region = Region(3, rows)
        for world in self.WORLDS:
            self.assertTrue(region.contains(world), world)


if __name__ == "__main__":
    unittest.main()
