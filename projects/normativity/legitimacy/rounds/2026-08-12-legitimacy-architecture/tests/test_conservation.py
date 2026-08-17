"""Conservation, non-laundering, and composition over the declared sweep."""

from __future__ import annotations

import unittest

from conservation import composition_sweep, sweep


class ConservationTests(unittest.TestCase):

    def test_every_answerable_sequence_has_exactly_one_fate(self):
        report = sweep(length=3)
        self.assertEqual(report.checked, 7 ** 3)
        self.assertGreater(report.answerable, 0)
        self.assertEqual(report.answerable, report.fate_total)
        self.assertEqual(report.answerable, report.fate_unique)

    def test_every_terminal_fate_carries_its_backing(self):
        report = sweep(length=3)
        self.assertEqual(report.laundered, ())
        self.assertGreater(report.terminal_backed, 0)

    def test_the_sweep_fails_on_its_null_input(self):
        """Strip the backing and every sequence that terminates or suspends must
        be refused.  A sweep that accepted everything either way would be
        confirming that the enumeration runs, not that the condition bites."""
        report = sweep(length=3, well_formed=False)
        self.assertEqual(report.checked, 7 ** 3)
        self.assertLess(report.answerable, report.checked)
        self.assertEqual(report.answerable, 3 ** 3)
        self.assertEqual(report.terminal_backed, 0)

    def test_representation_change_alone_never_terminates_a_liability(self):
        """The non-laundering half: churning the vocabulary at every step changes
        no fate, because identity is not carried by vocabulary."""
        plain = sweep(length=3)
        churned = sweep(length=3, vocabulary_churn=True)
        self.assertEqual(churned.laundered, ())
        self.assertEqual(plain.answerable, churned.answerable)
        self.assertEqual(plain.terminal_backed, churned.terminal_backed)


class CompositionTests(unittest.TestCase):

    def test_fate_composes(self):
        """The fate of a concatenation is determined by the first segment's fate
        and the second segment — the endpoint audit needs no replay."""
        report = composition_sweep(length=2)
        self.assertGreater(report.pairs, 0)
        self.assertEqual(report.disagreements, ())
        self.assertEqual(report.pairs, report.agreements)


if __name__ == "__main__":
    unittest.main()
