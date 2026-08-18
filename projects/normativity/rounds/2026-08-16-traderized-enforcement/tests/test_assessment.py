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


class NonemptinessIsNotAPrecondition(unittest.TestCase):
    """What (L3) buys is non-vacuity, not the construction.

    The source's scaling infimum is `EF.listMin` over the plausible worlds and
    `EF.listMin [] = EF.const 1`, so an empty assessment set scales by one. What
    goes empty with it is the set of plausible assessments, which is what the
    floor theorem and the exploitation criterion quantify over.
    """

    PROCESS = explicit([[]])

    def test_the_restriction_is_empty(self):
        self.assertEqual(self.PROCESS.restrict(0, PHI1), [])
        self.assertFalse(self.PROCESS.nonempty(0, PHI1))

    def test_the_scaling_is_neutral_rather_than_undefined(self):
        self.assertEqual(
            budgeter_scaling_on_support({"A": F(1)}, {"A": F(1, 2)}, {}, F(1, 10),
                                        self.PROCESS, 0, PHI1),
            F(1))

    def test_nesting_holds_vacuously(self):
        self.assertTrue(self.PROCESS.temporally_nested([0, 1], PHI1))


class ResurrectionBreaksTheFloor(unittest.TestCase):
    """Why nesting is load-bearing, at the quantity it is load-bearing for.

    The Budgeter's floor `-b` is proved by induction on the date, and the step
    needs a world assessed now to have been assessed before, so that the prior
    safety bound applies to it. Resurrect a world and the step fails: the trader
    is scaled by one at date `0` because the losing world is not assessed there,
    and the resurrected world then values the accumulated position below `-b`.
    """

    #: `A` false is dead at date 0 and alive again at date 1.
    PROCESS = explicit([
        [(F(1), F(0))],                        # date 0: only `A` true
        [(F(0), F(0)), (F(1), F(0))],          # date 1: `A` false resurrected
    ])
    POSITION = {"A": F(1)}                     # buy one share of `A`
    PRICES = {"A": F(1, 2)}
    BUDGET = F(1, 10)

    def test_the_process_fails_temporal_nesting(self):
        self.assertFalse(self.PROCESS.temporally_nested([0, 1], PHI1))

    def test_the_scaling_is_one_at_the_first_date(self):
        """Nothing assessed at date 0 loses on the buy, so nothing is scaled."""
        self.assertEqual(
            budgeter_scaling_on_support(self.POSITION, self.PRICES, {},
                                        self.BUDGET, self.PROCESS, 0, PHI1),
            F(1))

    def test_the_resurrected_world_is_below_the_budget(self):
        """Two dates of unscaled buying lose `1/2` each at `A` false, which is
        past `-b = -1/10` — the floor the source's part 2 asserts."""
        loss_per_date = F(0) - self.PRICES["A"]          # payout minus price
        self.assertEqual(loss_per_date, F(-1, 2))
        cumulative = 2 * loss_per_date
        self.assertEqual(cumulative, F(-1))
        self.assertLess(cumulative, -self.BUDGET)
        self.assertIn((F(0),), self.PROCESS.restrict(1, PHI1))


class SupportLocalNestingIsWeakerThanGlobal(unittest.TestCase):
    """The interface the lift consumes is the support-local shadow, and it is
    strictly weaker than `L_{t+1} subset L_t`.

    Ambient names `A`, `B`; the priced fragment is `{A}`. At date `0` the live
    worlds are those with `B` false; at date `1` they are those with `B` true.
    Global nesting fails outright. But every restriction to the priced fragment
    is matched, because `B` is not priced — which is exactly the situation the
    Lean witness `lateAllTrueLive` generalizes: a fresh unpriced coordinate
    absorbs the difference.
    """

    PROCESS = explicit([
        [(F(0), F(0)), (F(1), F(0))],          # date 0: `B` false
        [(F(0), F(1)), (F(1), F(1))],          # date 1: `B` true
    ])

    def test_global_nesting_fails(self):
        self.assertFalse(set(self.PROCESS.live(1)) <= set(self.PROCESS.live(0)))

    def test_support_local_nesting_holds_on_the_priced_fragment(self):
        self.assertTrue(self.PROCESS.temporally_nested([0, 1], PHI1))
        self.assertEqual(self.PROCESS.restrict(0, PHI1),
                         self.PROCESS.restrict(1, PHI1))

    def test_and_fails_once_the_unpriced_name_is_priced(self):
        """The shadow is relative to the queried support: price `B` and the
        difference is visible again. So the interface is genuinely weaker only
        for supports the construction does not query."""
        self.assertFalse(self.PROCESS.temporally_nested([0, 1], PHI2))

    def test_the_budgeter_cannot_tell_the_difference(self):
        for date in (0, 1):
            self.assertEqual(
                budgeter_scaling_on_support({"A": F(1)}, {"A": F(1, 2)}, {},
                                            F(1, 10), self.PROCESS, date, PHI1),
                F(1, 5), date)


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
