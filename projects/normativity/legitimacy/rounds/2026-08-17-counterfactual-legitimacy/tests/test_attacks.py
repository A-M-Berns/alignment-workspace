"""The six advisor-mediated attacks."""

from __future__ import annotations

import unittest

import scenarios as S
from noncapture import Z_FIVE, Z_FOUR, non_capture

RULES = ("repetition", "salience")


class AdvisorMediatedAttacks(unittest.TestCase):
    """Each attack keeps the record-internal conditions holding, fails the
    environment-relative target, and is rejected by reason-mediated non-capture
    for the right reason: the influenced arm's protected machinery differs from
    its coupled sibling's while the licensed reasons supplied are identical."""

    def test_all_six_keep_the_record_internal_conditions(self):
        for rule in RULES:
            for name, builder in S.ATTACKS.items():
                fixture, variation = builder(rule)
                for policy in variation:
                    report = fixture.run(policy).four()
                    with self.subTest(rule=rule, attack=name, arm=policy.name):
                        self.assertTrue(report.four, report.codes())
                        self.assertTrue(report.d.holds, report.codes())
                        self.assertTrue(report.x.holds, report.codes())

    def test_the_uninfluenced_arm_meets_the_target_and_the_other_does_not(self):
        for rule in RULES:
            for name, builder in S.ATTACKS.items():
                fixture, (null, influenced) = builder(rule)
                with self.subTest(rule=rule, attack=name):
                    self.assertTrue(fixture.run(null).target().legitimate)
                    self.assertFalse(fixture.run(influenced).target().legitimate)

    def test_the_licensed_reason_trace_is_empty_in_both_arms(self):
        """No attack works through a reason the practice licenses; each works
        through delivery.  That is what leaves non-capture something to say."""
        for rule in RULES:
            for name, builder in S.ATTACKS.items():
                fixture, variation = builder(rule)
                for policy in variation:
                    run = fixture.run(policy)
                    with self.subTest(rule=rule, attack=name, arm=policy.name):
                        self.assertEqual(set().union(*run.ltrace), set())

    def test_non_capture_rejects_every_attack(self):
        for rule in RULES:
            for name, builder in S.ATTACKS.items():
                fixture, variation = builder(rule)
                with self.subTest(rule=rule, attack=name):
                    self.assertTrue(non_capture(fixture, variation, Z_FIVE))

    def test_the_four_coordinate_projection_misses_distinction_collapse(self):
        """Attack I is the counterexample that forces the fifth coordinate.

        The advisor installs a merge licence.  That licence is not one of
        `generation`, `entitlement`, `bearing`, `adequacy`, so the four-field
        projection is identical across the arms and the condition passes on a
        trajectory that fails the target.  It is also not a field the procedural
        round's `State` carries, so none of its conditions could have seen it
        either.
        """
        for rule in RULES:
            fixture, variation = S.attack_i(rule)
            with self.subTest(rule=rule):
                self.assertEqual(non_capture(fixture, variation, Z_FOUR), ())
                self.assertTrue(non_capture(fixture, variation, Z_FIVE))

    def test_the_other_five_are_caught_by_the_four_coordinate_projection(self):
        for rule in RULES:
            for name, builder in S.ATTACKS.items():
                if name == "I":
                    continue
                fixture, variation = builder(rule)
                with self.subTest(rule=rule, attack=name):
                    self.assertTrue(non_capture(fixture, variation, Z_FOUR))


class TheResidualChannelIsWhatMakesTheConditionFalsifiable(unittest.TestCase):
    """A principal with no residual susceptibility satisfies the condition on
    every attack — and defeats every attack — because advisor input can then
    only enter through the reason port.

    Stated as a test rather than as a remark, because it is the exact sense in
    which the positive results above are not definitional: they are results
    about a transition rule with two channels, and they disappear when the
    second is removed."""

    def test_without_a_residual_channel_nothing_is_left_to_prosecute(self):
        for name, builder in S.ATTACKS.items():
            fixture, variation = builder("none")
            with self.subTest(attack=name):
                self.assertEqual(non_capture(fixture, variation, Z_FIVE), ())
                for policy in variation:
                    self.assertTrue(fixture.run(policy).target().legitimate)


if __name__ == "__main__":
    unittest.main()
