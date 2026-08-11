"""Tier B: the long tail of exact numbers carried forward from the source tree.

Per the Tier B philosophy of the previous consolidation, this retains the
*numerical assertions* rather than every historical implementation. Each number
below appeared in the source tree's own results and is recomputed here against
the folder-local implementations of Tier A. Where a number was produced by a
computation this package reimplements, the recomputation is the check; where it
was hand-derived, the closed form is stated and evaluated.

Passing is evidence for these displayed finite instances only.
"""

from __future__ import annotations

import unittest
from fractions import Fraction as Q

from src.composite import movement_recursion, wealth_cap
from src.core import single_row_coefficient
from src.grammar import CATALOG, evidence_classes, footprint_classes, legacy_classes


def positive_part(x: Q) -> Q:
    return max(Q(0), Q(x))


class MovementRecursionTests(unittest.TestCase):
    """The joint composition constants, at the displayed budgets."""

    THETA = Q(1, 10)
    QUOTE_ERROR = Q(1, 100)
    RISK = Q(1, 10)
    ORDINARY = Q(1, 5)

    def test_the_displayed_cap_sequence(self):
        caps = movement_recursion(self.THETA, self.QUOTE_ERROR, self.RISK,
                                  self.ORDINARY, 2)
        self.assertEqual(caps, (Q(1, 5), Q(31, 10), Q(321, 10)))

    def test_the_tightening_improvement_is_the_displayed_pair(self):
        """The retained headline: the cap improves from 321/10 to 31/10.

        The improvement is the difference between counting all book changes and
        counting only the core-invalidating ones: two changes against one.
        """
        caps = movement_recursion(self.THETA, self.QUOTE_ERROR, self.RISK,
                                  self.ORDINARY, 2)
        coarse, tightened = caps[2], caps[1]
        self.assertEqual((coarse, tightened), (Q(321, 10), Q(31, 10)))
        self.assertGreater(coarse, tightened)

    def test_the_recursion_is_the_stated_closed_form(self):
        kappa = (Q(1) - self.THETA) / self.THETA
        additive = self.QUOTE_ERROR / self.THETA + (kappa + Q(1)) * self.RISK
        expected = (Q(1) + kappa) * self.ORDINARY + additive
        self.assertEqual(movement_recursion(self.THETA, self.QUOTE_ERROR, self.RISK,
                                            self.ORDINARY, 1)[1], expected)

    def test_the_wealth_cap_composes_with_the_recursion(self):
        caps = movement_recursion(Q(1, 4), Q(0), Q(2), Q(0), 1)
        self.assertEqual(caps[1], Q(8))
        self.assertEqual(wealth_cap(Q(1, 4), Q(0), Q(2), caps[1]), Q(30))

    def test_the_bound_at_the_audited_pair_s_declared_minimum(self):
        caps = movement_recursion(Q(1, 10), Q(0), Q(2), Q(0), 1)
        self.assertEqual(caps[1], Q(20))
        self.assertEqual(wealth_cap(Q(1, 10), Q(0), Q(2), caps[1]), Q(198))

    def test_the_stage_factors(self):
        """Attained growth is `(1-theta)/theta`; the recursion charges one more."""
        for theta in (Q(1, 10), Q(1, 4), Q(1, 2)):
            with self.subTest(theta=theta):
                attained = (Q(1) - theta) / theta
                self.assertEqual(attained + Q(1), Q(1) / theta)


class CoreCertificateRepairTests(unittest.TestCase):
    """The numbers that displayed the unsound retention predicate and its repair.

    Setting: one coordinate, core coefficient `1/10`, incumbent reference `3/5`,
    base region `x >= 1/2`, and a change adding `x >= 3/5`.
    """

    THETA = Q(1, 10)
    REFERENCE = Q(3, 5)

    def test_the_bare_reference_is_admitted_while_its_core_is_cut(self):
        core_lower = self.REFERENCE * (Q(1) - self.THETA)
        self.assertEqual(core_lower, Q(27, 50))
        self.assertGreaterEqual(self.REFERENCE, Q(3, 5))
        self.assertLess(core_lower, Q(3, 5))

    def test_the_forced_successor_and_its_charge(self):
        forced = self.REFERENCE / (Q(1) - self.THETA)
        self.assertEqual(forced, Q(2, 3))
        holdings = Q(2)
        self.assertEqual(positive_part(holdings * (forced - self.REFERENCE)), Q(2, 15))

    def test_the_crossover_is_exact_at_one_sixth(self):
        """At `theta = 1/6` the core lower end is exactly the base constraint."""
        self.assertEqual(self.REFERENCE * (Q(1) - Q(1, 6)), Q(1, 2))

    def test_retention_is_coefficient_relative_not_shape_relative(self):
        """The same change retains at one coefficient and invalidates at another."""
        self.assertGreaterEqual(self.REFERENCE * (Q(1) - Q(1, 10)), Q(1, 2))
        self.assertLess(self.REFERENCE * (Q(1) - Q(1, 2)), Q(1, 2))


class CoreCoefficientClosedFormTests(unittest.TestCase):
    """The closed form `(M - r) / (M - m)`, at the retained instances."""

    def test_the_displayed_values(self):
        self.assertEqual(single_row_coefficient(Q(0), Q(1, 2), Q(1)), Q(1, 2))
        self.assertEqual(single_row_coefficient(Q(0), Q(1, 4), Q(1)), Q(3, 4))
        self.assertEqual(single_row_coefficient(Q(0), Q(3, 5), Q(1)), Q(2, 5))

    def test_an_unreachable_constraint_gives_zero(self):
        self.assertEqual(single_row_coefficient(Q(0), Q(1), Q(1)), Q(0))
        self.assertEqual(single_row_coefficient(Q(0), Q(1, 2), Q(1, 2)), Q(0))

    def test_the_post_settlement_collapse(self):
        """After the dependent settlement the row's range shrinks to `[0, 1/2]`."""
        self.assertEqual(single_row_coefficient(Q(0), Q(1, 2), Q(1, 2)), Q(0))


class GrammarClassificationTests(unittest.TestCase):
    """The classification counts the objection-grammar claim reports."""

    def test_the_counts(self):
        self.assertEqual(len(CATALOG), 12)
        self.assertEqual(len(footprint_classes(CATALOG)), 10)
        self.assertEqual(len(evidence_classes(CATALOG)), 9)
        self.assertEqual(len(legacy_classes(CATALOG)), 4)


class IncoherenceNumbersTests(unittest.TestCase):
    """The tolerance-clause numbers, restated as closed forms."""

    def test_the_three_price_instance(self):
        """`A + B - C = 1` against demanded `9/5`: excess `4/5` over three rows."""
        demanded = Q(9, 10) + Q(9, 10) - Q(0)
        identity = Q(1)
        self.assertEqual(demanded - identity, Q(4, 5))
        self.assertEqual((demanded - identity) / Q(3), Q(4, 15))

    def test_the_working_boundary_closed_form(self):
        """The robust lower end is `3/5 - tolerance` against a threshold of `1/2`."""
        self.assertEqual(Q(3, 5) - Q(1, 10), Q(1, 2))
        self.assertLess(Q(3, 5) - Q(1, 10) - Q(1, 240), Q(1, 2))


if __name__ == "__main__":
    unittest.main()
