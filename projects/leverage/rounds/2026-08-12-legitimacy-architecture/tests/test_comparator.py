"""The legitimacy-preserving comparator class, and when it has no content."""

from __future__ import annotations

import unittest

from comparator import (CONSTANT_FAMILY, PARTIAL_FAMILY, RESPONSES,
                        SEPARATING_FAMILY, analyse, collapses, core,
                        exhaustive_formula_check, uniform_class)


class CoreFormulaTests(unittest.TestCase):

    def test_the_product_formula_agrees_with_enumeration(self):
        """Checked over every family of three subsets of a three-element response
        space — 512 families, no sampling."""
        checked, disagreements = exhaustive_formula_check(size=3, length=3)
        self.assertEqual(checked, 8 ** 3)
        self.assertEqual(disagreements, 0)

    def test_a_constant_constraint_leaves_every_map_available(self):
        report = analyse(len(RESPONSES), CONSTANT_FAMILY)
        self.assertTrue(report.agrees)
        self.assertEqual(report.enumerated, 4 ** 4)
        self.assertTrue(report.constant_image)
        self.assertFalse(report.collapsed)


class CollapseTests(unittest.TestCase):

    def test_a_separating_constraint_family_collapses_to_the_identity(self):
        """The controlling negative: a constraint whose admissible set moves
        enough to pin down each response admits no non-trivial comparator, so a
        regret statement against the class is satisfied by doing nothing."""
        report = analyse(len(RESPONSES), SEPARATING_FAMILY)
        self.assertTrue(report.agrees)
        self.assertEqual(report.enumerated, 1)
        self.assertTrue(report.collapsed)
        self.assertEqual(uniform_class(len(RESPONSES), SEPARATING_FAMILY),
                         ((0, 1, 2, 3),))

    def test_partial_movement_leaves_a_non_trivial_class(self):
        """Collapse is not automatic: it is a computable property of the family."""
        report = analyse(len(RESPONSES), PARTIAL_FAMILY)
        self.assertTrue(report.agrees)
        self.assertFalse(report.collapsed)
        self.assertGreater(report.enumerated, 1)
        self.assertEqual(report.enumerated, 2 * 2 * 3 * 3)

    def test_collapse_is_exactly_the_pinning_condition(self):
        for family in (CONSTANT_FAMILY, SEPARATING_FAMILY, PARTIAL_FAMILY):
            pinned = all(core(4, family, a) == frozenset({a}) for a in range(4))
            self.assertEqual(collapses(4, family), pinned)
            self.assertEqual(len(uniform_class(4, family)) == 1, pinned)


if __name__ == "__main__":
    unittest.main()
