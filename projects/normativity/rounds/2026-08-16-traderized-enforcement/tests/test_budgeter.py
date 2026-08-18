"""The generalized Budgeter is a different function, not the same one."""
from __future__ import annotations

import unittest
from fractions import Fraction as F

from budgeter import scaling, shutoff
from market import Fragment, holdings_value

BOTH = [(F(0),), (F(1),)]          #: `A` false and `A` true
TRUE_ONLY = [(F(1),)]              #: a live-world process that has ruled `A` in


class TheWorldProcessChangesTheScaling(unittest.TestCase):
    """One sentence, a unit buy, a small budget, and two assessment processes."""

    POSITION = (F(1),)             # buy one share
    PRICES = (F(1, 2),)
    BUDGET = F(1, 10)
    PRIOR = {}

    def test_the_larger_process_scales_down(self):
        self.assertEqual(
            scaling(self.POSITION, self.PRICES, self.PRIOR, self.BUDGET, BOTH),
            F(1, 5))

    def test_the_smaller_process_does_not(self):
        self.assertEqual(
            scaling(self.POSITION, self.PRICES, self.PRIOR, self.BUDGET,
                    TRUE_ONLY), F(1))

    def test_so_the_realised_strategies_differ(self):
        big = scaling(self.POSITION, self.PRICES, self.PRIOR, self.BUDGET, BOTH)
        small = scaling(self.POSITION, self.PRICES, self.PRIOR, self.BUDGET,
                        TRUE_ONLY)
        self.assertNotEqual(big, small)
        self.assertEqual(tuple(big * x for x in self.POSITION), (F(1, 5),))
        self.assertEqual(tuple(small * x for x in self.POSITION), (F(1),))

    def test_the_damaging_world_is_the_one_dropped(self):
        """`A` false is where a unit buy loses, and it is exactly the world the
        smaller process no longer assesses."""
        self.assertEqual(holdings_value(self.POSITION, self.PRICES, (F(0),)),
                         F(-1, 2))
        self.assertEqual(holdings_value(self.POSITION, self.PRICES, (F(1),)),
                         F(1, 2))
        self.assertNotIn((F(0),), TRUE_ONLY)


class DeductiveSpecialization(unittest.TestCase):
    """When the live-world process equals `PC(D_t)`, the two agree."""

    FRAGMENT = Fragment(("phi", "notphi"), [lambda w: w[0] + w[1] == 1])

    def test_agreement_on_every_stage(self):
        position, prices, budget = (F(1), F(0)), (F(1, 2), F(1, 2)), F(1, 10)
        for settled in ({}, {"phi": 1}, {"phi": 0}):
            plausible = self.FRAGMENT.pc_worlds(settled)
            live = list(plausible)                     # C^D = Delta(PC(D))
            self.assertEqual(
                scaling(position, prices, {}, budget, plausible),
                scaling(position, prices, {}, budget, live), settled)

    def test_the_stages_are_not_all_the_same_set(self):
        sizes = [len(self.FRAGMENT.pc_worlds(s))
                 for s in ({}, {"phi": 1}, {"phi": 0})]
        self.assertEqual(sizes, [2, 1, 1])


class Preconditions(unittest.TestCase):

    def test_an_empty_process_gives_the_neutral_scaling(self):
        """The source's `EF.listMin []` is `EF.const 1`, so the Budgeter scales by
        one when nothing is assessed. Nonemptiness is not a precondition of the
        construction; it is what makes the floor theorem non-vacuous."""
        self.assertEqual(scaling((F(1),), (F(1, 2),), {}, F(1), []), F(1))

    def test_the_shutoff_reads_the_dates_process(self):
        """Nesting is what lets a world live now count as live then."""
        self.assertTrue(shutoff([{(F(0),): F(-2)}], F(1), [BOTH]))
        self.assertFalse(shutoff([{(F(0),): F(-2)}], F(1), [TRUE_ONLY]))


if __name__ == "__main__":
    unittest.main()
