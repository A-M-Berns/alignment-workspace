"""Controls.  A condition that only rejects the attacks has been fitted to them."""

from __future__ import annotations

import unittest

import scenarios as S
from noncapture import Z_FIVE, access, non_capture


class NonCaptureIsNotCorrectness(unittest.TestCase):
    """The principal reaches a bad view on its own.  The target fails; the
    counterfactual condition must not, or it is unusable for deference — an
    advisor cannot be asked to guarantee that the principal is right."""

    def test_autonomous_adequacy_widening_passes_while_the_target_fails(self):
        fixture, variation = S.autonomous_l()
        self.assertEqual(non_capture(fixture, variation, Z_FIVE), ())
        for policy in variation:
            self.assertFalse(fixture.run(policy).target().legitimate)

    def test_autonomous_bearing_drift_passes_while_the_target_fails(self):
        fixture, variation = S.autonomous_g()
        self.assertEqual(non_capture(fixture, variation, Z_FIVE), ())
        for policy in variation:
            self.assertFalse(fixture.run(policy).target().legitimate)


class RadicalTransformationIsPermitted(unittest.TestCase):
    """The procedural round's positive control, carried forward: concepts,
    standards, inquiry rules and verdict all change, and the environment agrees.
    A counterfactual condition that refused this would be refusing the learning
    the architecture exists to describe."""

    def test_k_passes_both_the_condition_and_the_target(self):
        fixture, variation = S.autonomous_k()
        self.assertEqual(non_capture(fixture, variation, Z_FIVE), ())
        self.assertEqual(access(fixture, variation), ())
        for policy in variation:
            self.assertTrue(fixture.run(policy).target().legitimate)


class PersuasionByLicensedReasons(unittest.TestCase):
    """Three arms: silence, a licensed reason, and the same licensed reason
    delivered loudly."""

    def setUp(self):
        self.fixture, (self.silent, self.reasoned,
                       self.loud) = S.licensed_persuasion()

    def test_the_licensed_reason_changes_the_protected_machinery(self):
        quiet = self.fixture.run(self.silent)
        moved = self.fixture.run(self.reasoned)
        self.assertNotEqual(Z_FIVE(quiet), Z_FIVE(moved))
        self.assertNotEqual(quiet.ltrace, moved.ltrace)

    def test_delivery_alone_changes_nothing(self):
        moved = self.fixture.run(self.reasoned)
        loud = self.fixture.run(self.loud)
        self.assertEqual(moved.ltrace, loud.ltrace)
        self.assertEqual(Z_FIVE(moved), Z_FIVE(loud))

    def test_the_condition_permits_all_three(self):
        variation = (self.silent, self.reasoned, self.loud)
        self.assertEqual(non_capture(self.fixture, variation, Z_FIVE), ())
        for policy in variation:
            report = self.fixture.run(policy).four()
            self.assertTrue(report.four and report.d.holds and report.x.holds)
            self.assertTrue(self.fixture.run(policy).target().legitimate)


class ResidualInfluenceIsRejected(unittest.TestCase):
    """The licensed-reason trace held fixed, a non-reason feature of the
    interaction varied, and the protected machinery moves."""

    def test_the_condition_fires_with_the_trace_held_fixed(self):
        fixture, variation = S.residual_placebo()
        runs = [fixture.run(policy) for policy in variation]
        self.assertEqual(runs[0].ltrace, runs[1].ltrace)
        self.assertNotEqual(Z_FIVE(runs[0]), Z_FIVE(runs[1]))
        self.assertTrue(non_capture(fixture, variation, Z_FIVE))
        self.assertEqual(access(fixture, variation), ())

    def test_the_record_internal_conditions_do_not_fire(self):
        fixture, variation = S.residual_placebo()
        for policy in variation:
            report = fixture.run(policy).four()
            self.assertTrue(report.four and report.d.holds and report.x.holds)


class ExposureThatChangesNothing(unittest.TestCase):

    def test_variation_below_the_threshold_passes(self):
        fixture, variation = S.no_effect()
        runs = [fixture.run(policy) for policy in variation]
        self.assertEqual(Z_FIVE(runs[0]), Z_FIVE(runs[1]))
        self.assertEqual(non_capture(fixture, variation, Z_FIVE), ())
        self.assertEqual(access(fixture, variation), ())
        for run in runs:
            self.assertTrue(run.target().legitimate)


if __name__ == "__main__":
    unittest.main()
