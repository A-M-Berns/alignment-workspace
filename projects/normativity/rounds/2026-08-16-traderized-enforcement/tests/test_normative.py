"""The motivating normative statics, and whether they discharge safety."""
from __future__ import annotations

import unittest
from fractions import Fraction as F

from core import indicator, maximal_theta
from deduction import world_deficit
from enforcement import EnforcementTrader, Region
from market import Fragment, holdings_value
from normative import (Endorsement, family_deficits, force_region,
                       liability_bound_at_date)

#: `NL-SI-A7`'s instance: three worlds, `A`/`B`/`C` true at one world each.
FRAGMENT = Fragment(("A", "B", "C"), [lambda w: w[0] + w[1] + w[2] == 1])
#: the book endorses that the first world carries probability at least a half
ENDORSEMENT = Endorsement("A", F(1, 2))
THETA = F(1, 4)


class TheTwoRowFamiliesDiffer(unittest.TestCase):
    """Settlement rows carry no liability; core rows carry all of it."""

    def test_settlement_rows_have_zero_deficit_at_every_assessed_world(self):
        for settled in ({}, {"B": 0}, {"B": 0, "C": 0}):
            worlds = FRAGMENT.pc_worlds(settled)
            settlement, _ = force_region(FRAGMENT, settled, [ENDORSEMENT], THETA)
            self.assertEqual(family_deficits(settlement, worlds), F(0), settled)

    def test_core_rows_carry_the_endorsement_gap(self):
        for settled, expected in (({}, F(1, 2)), ({"B": 0}, F(1, 2)),
                                  ({"B": 0, "C": 0}, F(0))):
            worlds = FRAGMENT.pc_worlds(settled)
            _, core = force_region(FRAGMENT, settled, [ENDORSEMENT], THETA)
            self.assertEqual(family_deficits(core, worlds), expected, settled)

    def test_the_gap_is_r_minus_the_worst_delivery(self):
        for settled in ({}, {"B": 0}, {"B": 0, "C": 0}):
            worlds = FRAGMENT.pc_worlds(settled)
            _, core = force_region(FRAGMENT, settled, [ENDORSEMENT], THETA)
            self.assertEqual(family_deficits(core, worlds),
                             ENDORSEMENT.exclusion_depth(FRAGMENT, worlds),
                             settled)

    def test_the_gap_does_not_depend_on_the_core_minimum(self):
        """`theta` sets how deep the reference must sit; it does not change how
        far the endorsement outruns the assessed worlds."""
        worlds = FRAGMENT.pc_worlds({})
        for theta in (F(1, 8), F(1, 4), F(1, 2)):
            _, core = force_region(FRAGMENT, {}, [ENDORSEMENT], theta)
            self.assertEqual(family_deficits(core, worlds), F(1, 2), theta)


class SettlementDrivesTheGapDown(unittest.TestCase):
    """Monotonicity is what the existing statics contribute."""

    STAGES = ({}, {"B": 0}, {"B": 0, "C": 0})

    def test_the_worst_delivery_is_non_decreasing(self):
        values = [ENDORSEMENT.worst_delivery(FRAGMENT,
                                             FRAGMENT.pc_worlds(s))
                  for s in self.STAGES]
        self.assertEqual(values, [F(0), F(0), F(1)])
        for earlier, later in zip(values, values[1:]):
            self.assertLessEqual(earlier, later)

    def test_so_the_exclusion_depth_is_non_increasing(self):
        depths = [ENDORSEMENT.exclusion_depth(FRAGMENT, FRAGMENT.pc_worlds(s))
                  for s in self.STAGES]
        self.assertEqual(depths, [F(1, 2), F(1, 2), F(0)])
        for earlier, later in zip(depths, depths[1:]):
            self.assertGreaterEqual(earlier, later)

    def test_vindication_is_where_the_depth_reaches_zero(self):
        """Once the record entails the endorsement, the core row admits every
        assessed world and the family becomes liability-free."""
        worlds = FRAGMENT.pc_worlds({"B": 0, "C": 0})
        self.assertEqual(ENDORSEMENT.worst_delivery(FRAGMENT, worlds), F(1))
        self.assertIsNone(maximal_theta(indicator(FRAGMENT, "A", worlds),
                                        ENDORSEMENT.rhs, worlds))


class SafeMotivatingTrajectory(unittest.TestCase):
    """The endorsement is vindicated by settlement after finitely many dates."""

    #: settles `B` then `C`, then nothing further changes
    STAGES = [{}, {"B": 0}] + [{"B": 0, "C": 0}] * 10

    def declarations(self):
        out = []
        for date, settled in enumerate(self.STAGES, start=1):
            worlds = FRAGMENT.pc_worlds(settled)
            settlement, core = force_region(FRAGMENT, settled, [ENDORSEMENT],
                                            THETA)
            out.append(dict(settlement=settlement, core=core, worlds=worlds,
                            slack=F(1, 2 ** (date + 1)), volume=F(date),
                            tolerance=F(1, 10)))
        return out

    def test_only_finitely_many_dates_carry_a_deficit(self):
        depths = [ENDORSEMENT.exclusion_depth(FRAGMENT,
                                              FRAGMENT.pc_worlds(s))
                  for s in self.STAGES]
        self.assertEqual([d for d in depths if d > 0], [F(1, 2), F(1, 2)])

    def test_the_cumulative_bound_is_finite(self):
        total = sum((liability_bound_at_date(**d) for d in self.declarations()),
                    F(0))
        self.assertEqual(total, F(135, 8))
        self.assertLess(total, F(17))

    def test_it_does_not_grow_with_the_horizon(self):
        first = sum((liability_bound_at_date(**d)
                     for d in self.declarations()[:4]), F(0))
        whole = sum((liability_bound_at_date(**d)
                     for d in self.declarations()), F(0))
        self.assertEqual(first, whole)


class UnsafeContrastTrajectory(unittest.TestCase):
    """Minimally altered: the endorsement is never vindicated."""

    STAGES = [{}] * 12          #: nothing ever settles

    def declarations(self):
        out = []
        for date, settled in enumerate(self.STAGES, start=1):
            worlds = FRAGMENT.pc_worlds(settled)
            settlement, core = force_region(FRAGMENT, settled, [ENDORSEMENT],
                                            THETA)
            out.append(dict(settlement=settlement, core=core, worlds=worlds,
                            slack=F(1, 2 ** (date + 1)), volume=F(date),
                            tolerance=F(1, 10)))
        return out

    def test_the_deficit_never_decays(self):
        depths = [ENDORSEMENT.exclusion_depth(FRAGMENT,
                                              FRAGMENT.pc_worlds(s))
                  for s in self.STAGES]
        self.assertEqual(set(depths), {F(1, 2)})

    def test_the_cumulative_bound_diverges_with_the_horizon(self):
        partials = []
        for horizon in (4, 8, 12):
            partials.append(sum((liability_bound_at_date(**d)
                                 for d in self.declarations()[:horizon]), F(0)))
        self.assertLess(partials[0], partials[1])
        self.assertLess(partials[1], partials[2])
        self.assertGreater(partials[2], F(300))

    def test_the_enforcement_position_really_loses_at_an_assessed_world(self):
        """Not only the bound: the position is short the endorsement's direction
        at a world the record still permits."""
        worlds = FRAGMENT.pc_worlds({})
        _, core = force_region(FRAGMENT, {}, [ENDORSEMENT], THETA)
        trader = EnforcementTrader(core, F(4))
        price = (F(1, 4), F(1, 2), F(1, 4))
        position = trader.coefficients(price)
        losing = [w for w in worlds
                  if holdings_value(position, price, w) < 0]
        self.assertTrue(losing)


if __name__ == "__main__":
    unittest.main()
