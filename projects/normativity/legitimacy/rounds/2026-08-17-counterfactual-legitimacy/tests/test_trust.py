"""The composition with the workspace's own trust-facing statement.

`GradeTrust` and `delegation_bridge` are recomputed from
`lean/Workspace/Deference/Contrib/DelegationBridge.lean` in exact rationals. The
Lean file imports grade trust as a hypothesis and its docstring records that no
settlement instantiation in the finite skeleton produces it. What this round can
add is not a derivation of it but a fact about how it can be made true.
"""

from __future__ import annotations

import unittest
from fractions import Fraction

import scenarios as S
import trust as T
from noncapture import Z_FIVE, non_capture
from response import alphabet_of, process_projection


class GradeTrustIsBuyable(unittest.TestCase):
    """`A`'s outcome model is fixed and wrong. In the uninfluenced arm the
    principal's grade contradicts it and grade trust fails. The advisor replaces
    the principal's adequacy relation, the grade lands exactly on the model, and
    grade trust holds at zero.

    Nothing in `GradeTrust` distinguishes this from competence, and
    `delegation_bridge` consumes it either way."""

    def setUp(self):
        self.fixture, (self.null, self.captured) = S.manufactured_trust()
        self.uninfluenced = T.trust_report(self.fixture.run(self.null),
                                           S.SUBSTANCE)
        self.influenced = T.trust_report(self.fixture.run(self.captured),
                                         S.SUBSTANCE)

    def test_the_advisor_decides_whether_its_own_trust_premise_holds(self):
        self.assertFalse(self.uninfluenced["grade_trust"])
        self.assertTrue(self.influenced["grade_trust"])

    def test_the_hypothesis_is_not_vacuous(self):
        """Where grade trust fails, the bridge's inequality fails too, so the
        hypothesis is doing work rather than being carried for form."""
        self.assertFalse(self.uninfluenced["bridge_holds"])
        self.assertTrue(self.influenced["bridge_holds"])

    def test_delegation_then_selects_what_the_environment_convicts(self):
        self.assertEqual(self.influenced["judgment"], {"c0": "pi-cheap"})
        self.assertEqual(self.influenced["delegate_value"], Fraction(1))
        self.assertFalse(self.fixture.run(self.captured).target().legitimate)
        self.assertTrue(self.fixture.run(self.null).target().legitimate)

    def test_the_record_internal_conditions_see_none_of_it(self):
        for policy in (self.null, self.captured):
            report = self.fixture.run(policy).four()
            self.assertTrue(report.four and report.d.holds and report.x.holds)

    def test_non_capture_is_what_sees_it(self):
        variation = (self.null, self.captured)
        alphabet = alphabet_of(self.fixture)
        self.assertTrue(non_capture(self.fixture, variation, Z_FIVE))
        self.assertTrue(non_capture(self.fixture, variation,
                                    process_projection(alphabet)))

    def test_the_grades_are_exactly_rational(self):
        for value in self.influenced["grade"].values():
            self.assertIsInstance(value, Fraction)


class GradeInvarianceUnderNonCapture(unittest.TestCase):
    """The statement the composition rests on.

    If the grade factors through the protected object, then coupled arms with
    equal licensed-reason traces have equal grades, so grade trust takes one
    value across the advisor's residual latitude. It is then a fact about the
    principal rather than something the advisor arranged."""

    def test_where_non_capture_holds_the_grade_is_invariant(self):
        for name, builder in (("autonomous-L", S.autonomous_l),
                              ("autonomous-G", S.autonomous_g),
                              ("K", S.autonomous_k),
                              ("no-effect", S.no_effect),
                              ("irrelevant-coordinate",
                               S.irrelevant_coordinate)):
            fixture, variation = builder()
            alphabet = alphabet_of(fixture)
            with self.subTest(scenario=name):
                self.assertEqual(non_capture(fixture, variation,
                                             process_projection(alphabet)), ())
                runs = [fixture.run(p) for p in variation]
                for other in runs[1:]:
                    self.assertTrue(
                        T.grade_factors_through(runs[0], other, S.SUBSTANCE))
                    self.assertEqual(
                        T.trust_report(runs[0], S.SUBSTANCE)["grade_trust"],
                        T.trust_report(other, S.SUBSTANCE)["grade_trust"])

    def test_where_it_fails_the_grade_is_not(self):
        fixture, variation = S.manufactured_trust()
        runs = [fixture.run(p) for p in variation]
        self.assertFalse(T.grade_factors_through(runs[0], runs[1], S.SUBSTANCE))


class TheFactorizationHypothesisIsLoadBearing(unittest.TestCase):
    """A grade reading a field outside the protected object.

    Every legitimacy clause is silent — nothing the advisor wrote answers a
    normative question — and grade trust flips anyway. So the composition needs
    'the grade factors through the protected object' as a stated premise, and
    that premise is what fixes how much the protected object must cover."""

    def setUp(self):
        self.fixture, self.variation = S.grade_reads_outside()

    def test_every_legitimacy_clause_is_silent(self):
        alphabet = alphabet_of(self.fixture)
        from coverage import covered
        from noncapture import access
        self.assertEqual(non_capture(self.fixture, self.variation,
                                     process_projection(alphabet)), ())
        self.assertEqual(access(self.fixture, self.variation), ())
        self.assertTrue(covered(self.fixture, self.variation))

    def test_and_grade_trust_flips_anyway(self):
        first, second = (self.fixture.run(p) for p in self.variation)
        self.assertFalse(T.trust_report_outside(first)["grade_trust"])
        self.assertTrue(T.trust_report_outside(second)["grade_trust"])


if __name__ == "__main__":
    unittest.main()
