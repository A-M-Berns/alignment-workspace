"""What reason mediation cannot reach, and what the second clause costs."""

from __future__ import annotations

import unittest

import scenarios as S
from legitimacy import legitimate as composed, target_holds
from noncapture import (Z_FIVE, access, non_capture, uncoupled_pairs, withheld)


class SelectionAmongLicensedReasons(unittest.TestCase):
    """The kill test.

    Both grounds are provenance-valid and both bear on adequacy under the
    principal's own relation, so an advisor that supplies one and withholds the
    other obtains a protected effect entirely within the licensed.  The delivered
    traces then differ, and reason mediation has nothing to say."""

    def setUp(self):
        self.fixture, (self.full, self.selective) = S.selective_information()

    def test_the_withheld_reason_is_genuinely_licensed(self):
        run = self.fixture.run(self.full)
        self.assertIn(("audit-finding", "adequacy"), set().union(*run.ltrace))
        self.assertIn(("efficiency-review", "adequacy"),
                      set().union(*run.ltrace))

    def test_selection_defeats_the_target_with_every_other_clause_holding(self):
        report = self.fixture.run(self.selective).four()
        self.assertTrue(report.four and report.d.holds and report.x.holds)
        self.assertFalse(self.fixture.run(self.selective).target().legitimate)
        self.assertTrue(self.fixture.run(self.full).target().legitimate)

    def test_reason_mediation_does_not_fire(self):
        variation = (self.full, self.selective)
        self.assertEqual(non_capture(self.fixture, variation, Z_FIVE), ())

    def test_protected_access_does_fire(self):
        variation = (self.full, self.selective)
        self.assertTrue(access(self.fixture, variation))
        self.assertEqual(withheld(self.fixture, self.selective),
                         ((1, (("audit-finding", "adequacy"),)),))
        self.assertEqual(withheld(self.fixture, self.full), ())


class ControllingWhatArises(unittest.TestCase):
    """The case the procedural round recorded as unattacked.

    Suppressing the encounter defeats the target while leaving the protected
    machinery and the licensed-reason trace identical.  Reason mediation is not
    merely silent here: the pair is not coupled, because the exogenous history
    is exactly what coupling holds fixed.  So the coupling relation's
    'same exogenous encounters' clause is not a modelling convenience — it *is*
    the assumption that the advisor does not control what arises."""

    def setUp(self):
        self.fixture, (self.null, self.suppress) = S.controls_what_arises()

    def test_suppression_defeats_the_target(self):
        report = self.fixture.run(self.suppress).four()
        self.assertTrue(report.four and report.d.holds and report.x.holds)
        self.assertFalse(self.fixture.run(self.suppress).target().legitimate)
        self.assertTrue(self.fixture.run(self.null).target().legitimate)

    def test_the_protected_state_and_the_trace_are_identical(self):
        first, second = (self.fixture.run(self.null),
                         self.fixture.run(self.suppress))
        self.assertEqual(Z_FIVE(first), Z_FIVE(second))
        self.assertEqual(first.ltrace, second.ltrace)

    def test_the_pair_is_not_coupled_and_the_class_reports_it(self):
        variation = (self.null, self.suppress)
        self.assertFalse(self.fixture.coupled(self.null, self.suppress))
        self.assertEqual(non_capture(self.fixture, variation, Z_FIVE), ())
        self.assertEqual(uncoupled_pairs(self.fixture, variation),
                         (("null", "suppress"),))

    def test_protected_access_covers_it(self):
        self.assertTrue(access(self.fixture, (self.null, self.suppress)))


class AccessDoesNotImportTheTarget(unittest.TestCase):
    """One fixture, one variation class, two environments differing only in
    whether the cheap witness really settles the demand.

    Both counterfactual clauses take one value across the pair; `L*` takes two.
    So what protected access needs from outside the record is an exogenous
    supply of due inputs, not the environment that adjudicates faithfulness —
    the two are independent objects, and a round that conflated them would have
    graded this result as a failure."""

    def test_the_clauses_are_constant_where_the_target_is_not(self):
        fixture, variation, faithful, unfaithful = \
            S.record_equivalent_environments()
        self.assertEqual(non_capture(fixture, variation, Z_FIVE), ())
        self.assertTrue(access(fixture, variation))
        selective = fixture.run(variation[1])
        self.assertTrue(selective.target_against(faithful).legitimate)
        self.assertFalse(selective.target_against(unfaithful).legitimate)


class TheJointInterface(unittest.TestCase):
    """All four clauses, against every scenario the round builds.

    Rejection is the correct verdict where the environment-relative target
    fails through something the interface is meant to reach; acceptance is
    correct everywhere else, including where the target fails through the
    principal's own error under full inquiry.
    """

    REJECTED = ("C", "E", "G", "H", "I", "L", "selective", "arises",
                "transient", "deprivation", "creates", "manufactured-trust")
    ACCEPTED = ("autonomous-L", "autonomous-G", "K", "persuasion", "no-effect",
                "novel-reason", "irrelevant-coordinate",
                "autonomous-L-covered", "persuasion-covered")

    def scenarios(self):
        built = {name: builder() for name, builder in S.ATTACKS.items()}
        built.update({
            "selective": S.selective_information(),
            "arises": S.controls_what_arises(),
            "transient": S.transient_capture(),
            "deprivation": S.universal_deprivation(),
            "creates": S.advisor_creates_circumstances(),
            "manufactured-trust": S.manufactured_trust(),
            "autonomous-L": S.autonomous_l(),
            "autonomous-G": S.autonomous_g(),
            "K": S.autonomous_k(),
            "persuasion": S.licensed_persuasion(),
            "no-effect": S.no_effect(),
            "novel-reason": S.novel_reason(),
            "irrelevant-coordinate": S.irrelevant_coordinate(),
            "autonomous-L-covered": S.autonomous_error_under_full_inquiry(),
            "persuasion-covered": S.persuasion_under_full_inquiry(),
        })
        return built

    def test_every_scenario_gets_the_verdict_it_should(self):
        built = self.scenarios()
        self.assertEqual(sorted(built), sorted(self.REJECTED + self.ACCEPTED))
        for name, (fixture, variation) in built.items():
            with self.subTest(scenario=name):
                self.assertEqual(composed(fixture, variation),
                                 name in self.ACCEPTED)

    def test_the_target_and_the_interface_disagree_in_exactly_one_direction(self):
        """Legitimate-and-failing-the-target is the intended case; the reverse —
        illegitimate while the target holds on every arm — occurs in no scenario
        here, and the round does not claim it cannot occur."""
        for name, (fixture, variation) in self.scenarios().items():
            with self.subTest(scenario=name):
                if not composed(fixture, variation):
                    continue
                if target_holds(fixture, variation):
                    continue
                self.assertIn(name, ("autonomous-L", "autonomous-G",
                                     "autonomous-L-covered"))


if __name__ == "__main__":
    unittest.main()
