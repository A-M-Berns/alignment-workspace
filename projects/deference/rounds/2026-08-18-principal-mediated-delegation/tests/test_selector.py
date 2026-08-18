"""The composition with the counterfactual-legitimacy round, and its limits."""

from __future__ import annotations

import inspect
import unittest

import fixtures
import scenarios
import selector as sel
from fixture import Fixture, Policy, SUBSTANCE


def _discover() -> tuple[str, ...]:
    """Every scenario of that round shaped `(Fixture, policies)`.

    Discovered rather than listed, so a scenario added there is composed with
    here without anyone remembering, and so this test cannot quietly shrink to
    the cases that pass.
    """
    found = []
    for name, function in sorted(vars(scenarios).items()):
        if not inspect.isfunction(function) or function.__module__ != "scenarios":
            continue
        try:
            produced = function()
        except TypeError:
            continue
        if (isinstance(produced, tuple) and len(produced) >= 2
                and isinstance(produced[0], Fixture)
                and isinstance(produced[1], tuple)
                and all(isinstance(p, Policy) for p in produced[1])):
            found.append(name)
    return tuple(found)


SCENARIOS = _discover()


def variation(name):
    produced = getattr(scenarios, name)()
    return produced[0], produced[1]


class TheComposition(unittest.TestCase):
    """`PR39 non-capture of Z` + `D factors through Z` -> residual invariance of D."""

    def test_the_selector_factors_through_the_protected_process(self):
        """Wherever two arms agree on the protected process they agree on the
        selector, along the run and not only at the endpoint.

        This is the factorization premise, checked over every scenario rather
        than assumed. It is what makes the composition a composition: the
        legitimacy round proves things about `Z`, and nothing about `Z` reaches
        the selector without it.
        """
        for name in SCENARIOS:
            with self.subTest(name):
                fixture, policies = variation(name)
                self.assertEqual(
                    sel.selector_invariant(fixture, policies, SUBSTANCE), ())

    def test_selector_capture_implies_process_capture(self):
        """Every pair whose selector moves at equal licensed traces is a pair the
        legitimacy round's own non-capture clause already rejects.

        The composition read forwards. It is a one-way implication and the test
        below shows the converse fails.
        """
        for name in SCENARIOS:
            with self.subTest(name):
                fixture, policies = variation(name)
                captured = set(sel.residual_capture(fixture, policies, SUBSTANCE))
                rejected = {tuple(sorted(pair)) for pair in
                            sel.non_capture_of_process(fixture, policies)}
                for pair in captured:
                    self.assertIn(tuple(sorted(pair)), rejected, name)

    def test_the_implication_is_strict(self):
        """Process non-capture is sufficient for selector invariance and not
        necessary: an advisor can move the protected process without moving the
        selector, and two scenarios do."""
        moved_process_only = []
        for name in SCENARIOS:
            fixture, policies = variation(name)
            if (sel.non_capture_of_process(fixture, policies)
                    and not sel.residual_capture(fixture, policies, SUBSTANCE)):
                moved_process_only.append(name)
        self.assertIn("transient_capture", moved_process_only)
        self.assertIn("residual_placebo", moved_process_only)

    def test_the_composition_is_not_vacuous(self):
        """At least one scenario actually moves the selector, so the invariance
        results above are not about a constant function."""
        fixture, policies = variation("manufactured_trust")
        self.assertNotEqual(
            sel.residual_capture(fixture, policies, SUBSTANCE), ())

    def test_the_factorization_premise_is_load_bearing(self):
        """A selector reading a field the protected object does not cover flips
        while every legitimacy clause stays silent.

        The analogue of that round's `grade_reads_outside` witness for the grade,
        and it says the same thing: `D = f(Z)` is a premise and not free.
        """
        fixture, policies = variation("grade_reads_outside")
        self.assertEqual(sel.non_capture_of_process(fixture, policies), ())
        outside = {policy.name: tuple(sel.selector_outside(m)
                                      for m in fixture.run(policy).states)
                   for policy in policies}
        self.assertEqual(len(set(outside.values())), 2)

    def test_the_endpoint_is_not_enough(self):
        """Push-then-restore leaves the endpoint selector identical.

        Every selector statement in this round is taken along the run, for the
        reason that round gives for taking the protected object along it.
        """
        fixture, policies = variation("transient_capture")
        endpoints = {sel.selector_along(fixture.run(p), SUBSTANCE)[-1]
                     for p in policies}
        self.assertEqual(len(endpoints), 1)


class LegitimatePersuasion(unittest.TestCase):
    def test_a_licensed_reason_may_move_the_selector(self):
        """The control the interface must not forbid.

        A licensed reason at the same coordinate, under the principal's own
        bearing relation, changes which choice the principal makes. Neither
        clause fires.
        """
        fixture, policies = fixtures.persuasion_moves_the_selector()
        selectors = {p.name: sel.selector_along(fixture.run(p), SUBSTANCE)
                     for p in policies}
        self.assertEqual(len(set(selectors.values())), 2)
        self.assertEqual(sel.non_capture_of_process(fixture, policies), ())
        self.assertEqual(sel.residual_capture(fixture, policies, SUBSTANCE), ())


class PredictionAgainstControl(unittest.TestCase):
    def test_perfect_prediction_is_separated_from_control(self):
        episode = fixtures.perfect_prediction()
        delegate, preemptor = fixtures.perfect_prediction_pair(episode)
        self.assertTrue(sel.realized_agree(episode, delegate, preemptor))
        self.assertTrue(sel.prediction_is_not_control(episode, delegate, preemptor))

    def test_responding_to_the_choice_is_weaker_than_deferring_to_it(self):
        episode = fixtures.perfect_prediction()
        delegate, _ = fixtures.perfect_prediction_pair(episode)
        overrider = fixtures.systematic_overrider(episode)
        self.assertTrue(sel.dependence_is_not_ownership(episode, delegate, overrider))

    def test_the_separation_is_not_available_from_the_realized_data(self):
        """Stated as the negative it is: the realized quantity, the realized
        choice and the value all agree, and only the map differs."""
        from model import value
        episode = fixtures.perfect_prediction()
        delegate, preemptor = fixtures.perfect_prediction_pair(episode)
        self.assertEqual(value(episode, delegate), value(episode, preemptor))
