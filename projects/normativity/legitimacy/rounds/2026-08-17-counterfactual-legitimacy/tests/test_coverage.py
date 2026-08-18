"""Anti-selection and adequacy are two properties."""

from __future__ import annotations

import unittest

import scenarios as S
from coverage import coverage, covered, undelivered, unserviced
from noncapture import Z_FIVE, access, non_capture
from response import alphabet_of, process_projection


class UniversalDeprivation(unittest.TestCase):
    """Every policy in the class withholds the same due reason.

    Protected access compares policies, so a uniform class satisfies it. The
    process still never receives what it was owed, and the target fails."""

    def setUp(self):
        self.fixture, self.variation = S.universal_deprivation()

    def test_both_counterfactual_clauses_pass(self):
        alphabet = alphabet_of(self.fixture)
        self.assertEqual(non_capture(self.fixture, self.variation, Z_FIVE), ())
        self.assertEqual(non_capture(self.fixture, self.variation,
                                     process_projection(alphabet)), ())
        self.assertEqual(access(self.fixture, self.variation), ())

    def test_the_record_internal_conditions_pass_and_the_target_fails(self):
        for policy in self.variation:
            run = self.fixture.run(policy)
            report = run.four()
            self.assertTrue(report.four and report.d.holds and report.x.holds)
            self.assertFalse(run.target().legitimate)

    def test_coverage_is_what_catches_it(self):
        self.assertFalse(covered(self.fixture, self.variation))
        for policy in self.variation:
            self.assertEqual(coverage(self.fixture, policy),
                             ("coverage.due_reason_never_delivered",))
            self.assertTrue(undelivered(self.fixture, policy))

    def test_coverage_does_not_attribute(self):
        """The two arms are indistinguishable, so nothing here says whether the
        deprivation is the advisor's doing or the world's."""
        first, second = self.variation
        self.assertEqual(coverage(self.fixture, first),
                         coverage(self.fixture, second))


class CoverageIsARunProperty(unittest.TestCase):
    """Unlike the two counterfactual clauses, one realized run determines it —
    which is why it cannot do their job, and why it is the only clause of the
    interface an ordinary audit can check."""

    def test_it_is_determined_by_a_single_arm(self):
        fixture, variation = S.selective_information()
        verdicts = {p.name: coverage(fixture, p) for p in variation}
        self.assertEqual(verdicts["full"], ())
        self.assertEqual(verdicts["selective"],
                         ("coverage.due_reason_never_delivered",))

    def test_unserviced_demands_are_visible_without_an_environment_relation(self):
        fixture, (null, suppress) = S.controls_what_arises()
        self.assertEqual(unserviced(fixture.run(null)), ())
        self.assertEqual(unserviced(fixture.run(suppress)), ("s-harm",))


class CoverageDoesNotForbidLegitimateBehaviour(unittest.TestCase):

    def test_autonomous_error_under_full_inquiry_is_covered(self):
        fixture, variation = S.autonomous_error_under_full_inquiry()
        self.assertTrue(covered(fixture, variation))
        for policy in variation:
            self.assertFalse(fixture.run(policy).target().legitimate)

    def test_persuasion_under_full_inquiry_is_covered(self):
        fixture, variation = S.persuasion_under_full_inquiry()
        self.assertTrue(covered(fixture, variation))
        self.assertEqual(access(fixture, variation), ())
        for policy in variation:
            self.assertTrue(fixture.run(policy).target().legitimate)

    def test_a_novel_reason_is_neither_selection_nor_a_coverage_failure(self):
        fixture, variation = S.novel_reason()
        alphabet = alphabet_of(fixture)
        self.assertTrue(covered(fixture, variation))
        self.assertEqual(access(fixture, variation), ())
        self.assertEqual(non_capture(fixture, variation,
                                     process_projection(alphabet)), ())


class CreatingAndSuppressingCircumstances(unittest.TestCase):
    """The advisor decides whether the occasion arises.

    The model carries one channel for both readings and does not separate
    creating an occasion from removing one; the pair is uncoupled either way,
    and access and coverage both fire on the arm where nothing arises."""

    def test_the_arm_where_nothing_arises_fails_coverage(self):
        fixture, (nothing, raised) = S.advisor_creates_circumstances()
        self.assertEqual(coverage(fixture, raised), ())
        self.assertEqual(coverage(fixture, nothing),
                         ("coverage.due_demand_never_serviced",
                          "coverage.encounter_never_arose"))
        self.assertFalse(fixture.coupled(nothing, raised))
        self.assertTrue(access(fixture, (nothing, raised)))


if __name__ == "__main__":
    unittest.main()
