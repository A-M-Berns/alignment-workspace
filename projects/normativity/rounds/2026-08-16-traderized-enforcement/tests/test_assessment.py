"""The assessment process across a growing priced fragment."""
from __future__ import annotations

import unittest
from fractions import Fraction as F

from assessment import (AssessmentProcess, budgeter_scaling_on_support,
                        deductive_process)
from budgeter import scaling

#: The ambient world space is fixed; only the priced fragment grows.
NAMES = ("A", "B")
PHI1 = ("A",)
PHI2 = ("A", "B")


def explicit(live_by_date):
    return AssessmentProcess(NAMES, lambda t: live_by_date[min(t, len(live_by_date) - 1)])


class TheWorldSpaceDoesNotChange(unittest.TestCase):
    """Which is why temporal nesting is well-typed in the first place."""

    def test_restrictions_are_taken_of_total_worlds(self):
        process = explicit([[(F(0), F(0)), (F(0), F(1)), (F(1), F(1))]])
        self.assertEqual(process.restrict(0, PHI2),
                         [(F(0), F(0)), (F(0), F(1)), (F(1), F(1))])
        self.assertEqual(process.restrict(0, PHI1), [(F(0),), (F(1),)])

    def test_restriction_deduplicates(self):
        """Two worlds agreeing on the support give one restricted world."""
        process = explicit([[(F(0), F(0)), (F(0), F(1))]])
        self.assertEqual(len(process.restrict(0, PHI2)), 2)
        self.assertEqual(process.restrict(0, PHI1), [(F(0),)])


class GrowingFragment(unittest.TestCase):
    """Later live worlds restrict into the earlier live set."""

    PROCESS = explicit([
        [(F(0), F(0)), (F(0), F(1)), (F(1), F(0)), (F(1), F(1))],   # date 0
        [(F(0), F(0)), (F(0), F(1)), (F(1), F(1))],                 # date 1
        [(F(0), F(1)), (F(1), F(1))],                               # date 2
    ])

    def test_restrictions_nest_on_the_smaller_fragment(self):
        self.assertTrue(self.PROCESS.temporally_nested([0, 1, 2], PHI1))

    def test_restrictions_nest_on_the_larger_fragment(self):
        self.assertTrue(self.PROCESS.temporally_nested([0, 1, 2], PHI2))

    def test_the_later_live_set_restricted_sits_inside_the_earlier(self):
        later = set(self.PROCESS.restrict(2, PHI1))
        earlier = set(self.PROCESS.restrict(0, PHI1))
        self.assertTrue(later <= earlier)
        self.assertEqual(later, {(F(0),), (F(1),)})

    def test_restriction_consistency_holds(self):
        for date in (0, 1, 2):
            self.assertTrue(
                self.PROCESS.restriction_consistent(date, PHI1, PHI2), date)

    def test_nonemptiness_on_both_supports(self):
        for date in (0, 1, 2):
            self.assertTrue(self.PROCESS.nonempty(date, PHI1))
            self.assertTrue(self.PROCESS.nonempty(date, PHI2))


class TheFailureCaseIsRejected(unittest.TestCase):
    """A later world whose restriction was not live earlier."""

    PROCESS = explicit([
        [(F(0), F(0)), (F(0), F(1))],          # date 0: `A` is false everywhere
        [(F(0), F(0)), (F(1), F(1))],          # date 1: `A` true appears
    ])

    def test_the_larger_support_is_not_nested(self):
        self.assertFalse(self.PROCESS.temporally_nested([0, 1], PHI2))

    def test_and_neither_is_the_smaller_one(self):
        self.assertFalse(self.PROCESS.temporally_nested([0, 1], PHI1))
        self.assertNotIn((F(1),), self.PROCESS.restrict(0, PHI1))
        self.assertIn((F(1),), self.PROCESS.restrict(1, PHI1))

    def test_restriction_consistency_still_holds_within_a_date(self):
        """The two conditions are independent: this process is restriction
        consistent and fails only temporal nesting."""
        for date in (0, 1):
            self.assertTrue(
                self.PROCESS.restriction_consistent(date, PHI1, PHI2), date)


class BudgeterConsumesTheRestriction(unittest.TestCase):
    """A strategy supported on `{A}` queries the live process on `{A}`."""

    PROCESS = explicit([
        [(F(0), F(0)), (F(0), F(1)), (F(1), F(0)), (F(1), F(1))],
        [(F(1), F(0)), (F(1), F(1))],          # `A` has been settled true
    ])
    POSITION = {"A": F(1)}
    PRICES = {"A": F(1, 2)}
    BUDGET = F(1, 10)

    def test_the_restriction_is_what_is_queried(self):
        self.assertEqual(self.PROCESS.restrict(0, PHI1), [(F(0),), (F(1),)])
        self.assertEqual(self.PROCESS.restrict(1, PHI1), [(F(1),)])

    def test_the_scaling_matches_the_explicit_computation(self):
        for date, expected in ((0, F(1, 5)), (1, F(1))):
            self.assertEqual(
                budgeter_scaling_on_support(self.POSITION, self.PRICES, {},
                                            self.BUDGET, self.PROCESS, date,
                                            PHI1),
                expected, date)

    def test_it_agrees_with_the_support_free_budgeter(self):
        for date in (0, 1):
            restricted = self.PROCESS.restrict(date, PHI1)
            self.assertEqual(
                budgeter_scaling_on_support(self.POSITION, self.PRICES, {},
                                            self.BUDGET, self.PROCESS, date,
                                            PHI1),
                scaling((F(1),), (F(1, 2),), {}, self.BUDGET, restricted), date)

    def test_duplicate_worlds_do_not_change_the_answer(self):
        """The value depends only on the restriction, which is why restricting
        is the right finite quotient rather than a lossy shortcut."""
        doubled = explicit([[(F(0), F(0)), (F(0), F(1)), (F(1), F(0)),
                             (F(1), F(1))]])
        self.assertEqual(doubled.restrict(0, PHI1), [(F(0),), (F(1),)])
        self.assertEqual(
            budgeter_scaling_on_support(self.POSITION, self.PRICES, {},
                                        self.BUDGET, doubled, 0, PHI1),
            F(1, 5))


class DeductiveInstance(unittest.TestCase):
    """Deduction supplies the interface over two growing fragments."""

    PROCESS = deductive_process(
        NAMES, [], [{}, {"A": 1}, {"A": 1, "B": 1}])

    def test_temporal_nesting_on_both_supports(self):
        self.assertTrue(self.PROCESS.temporally_nested([0, 1, 2], PHI1))
        self.assertTrue(self.PROCESS.temporally_nested([0, 1, 2], PHI2))

    def test_restriction_consistency_on_every_stage(self):
        for date in (0, 1, 2):
            self.assertTrue(
                self.PROCESS.restriction_consistent(date, PHI1, PHI2), date)

    def test_nonemptiness_under_consistency(self):
        for date in (0, 1, 2):
            self.assertTrue(self.PROCESS.nonempty(date, PHI2), date)

    def test_the_stages_genuinely_shrink(self):
        sizes = [len(self.PROCESS.restrict(d, PHI2)) for d in (0, 1, 2)]
        self.assertEqual(sizes, [4, 2, 1])

    def test_an_inconsistent_stage_is_empty(self):
        broken = deductive_process(NAMES, [lambda w: w[0] + w[1] == 1],
                                   [{"A": 1, "B": 1}])
        self.assertFalse(broken.nonempty(0, PHI2))


if __name__ == "__main__":
    unittest.main()
