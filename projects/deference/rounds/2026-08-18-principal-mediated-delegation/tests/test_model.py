"""The typing itself: what it can express, and what it refuses to carry."""

from __future__ import annotations

import unittest
from fractions import Fraction

import fixtures
from model import (Conduct, constant_channel, identity_channel, mediated,
                   mediates, permuted_channel, preemptive, realized_choice,
                   realized_quantity, response_map, responds_to_the_choice,
                   value, well_formed)


class TheTyping(unittest.TestCase):
    def test_every_quantity_is_an_exact_rational(self):
        for build in (fixtures.perfect_prediction, fixtures.committed_preparation,
                      fixtures.override_after_full_update,
                      fixtures.foreclosing_preparation,
                      fixtures.ceremonial_choice, fixtures.two_cell):
            episode = build()
            for quantity in episode.quantity.values():
                self.assertIsInstance(quantity, Fraction)
            for grade in episode.grade.values():
                self.assertIsInstance(grade, Fraction)

    def test_deference_is_read_off_the_channel_and_is_not_a_field(self):
        """There is no authorization coordinate to set, so nothing can spoof one.

        `mediates` is a predicate of the channel. Two conducts agreeing on
        preparation, channel and implementation have the same verdict whatever
        else is attached to them, which is the finite form of the moral of
        `lean/Workspace/Deference/Contrib/StaticViewFactorization.lean`:
        authorization has to enter before the factorization boundary, and here it
        is the boundary.
        """
        episode = fixtures.perfect_prediction()
        delegate, _ = fixtures.perfect_prediction_pair(episode)
        relabelled = fixtures.with_unread_payload(delegate, "authorized=true")
        self.assertEqual(mediated(episode, delegate),
                         mediated(episode, relabelled))
        self.assertEqual(value(episode, delegate), value(episode, relabelled))
        self.assertEqual(response_map(episode, delegate),
                         response_map(episode, relabelled))

    def test_a_conduct_that_writes_the_choice_is_not_mediated(self):
        episode = fixtures.perfect_prediction()
        delegate, preemptor = fixtures.perfect_prediction_pair(episode)
        self.assertTrue(mediated(episode, delegate))
        self.assertTrue(preemptive(episode, preemptor))

    def test_a_permuting_channel_responds_and_does_not_defer(self):
        """The separation the Cartesian-frame register cannot make.

        `simRead not` is homotopy equivalent to `delegated` in
        `CartesianFrameBridge.lean`, so there varying with the principal is not
        separated from deferring to it. Here it is: the overrider's response map
        is nonconstant and its channel is not the identity.
        """
        episode = fixtures.perfect_prediction()
        overrider = fixtures.systematic_overrider(episode)
        self.assertTrue(responds_to_the_choice(episode, overrider))
        self.assertFalse(mediated(episode, overrider))

    def test_every_conduct_used_is_well_formed(self):
        episode = fixtures.two_cell()
        for conduct in (fixtures.token_responsive(episode),
                        fixtures.fully_deferring(episode)):
            self.assertTrue(well_formed(episode, conduct), conduct.name)

    def test_a_foreclosing_preparation_makes_mediation_vacuous(self):
        """Nothing about the channel catches foreclosure.

        With one option left the identity is the only map on it, so `mediates`
        holds and says nothing. This is why the interface has an efficacy clause
        and why `repair.py` reports a separate foreclosure term.
        """
        episode = fixtures.foreclosing_preparation()
        seizing = Conduct("seize-and-defer", {"c0": "seize"},
                          identity_channel(episode),
                          {("c0", d): "u0" for d in episode.choices})
        self.assertTrue(mediates(episode, seizing, "c0"))
        self.assertTrue(episode.preparation("seize").forecloses(episode.choices))

    def test_the_selector_is_the_least_maximiser_in_the_fixed_order(self):
        episode = fixtures.ceremonial_choice()
        for state in episode.states:
            chosen = episode.selector(state, "keep")
            best = max(episode.grade[(state, d)] for d in episode.choices)
            self.assertEqual(episode.grade[(state, chosen)], best)
            for earlier in episode.choices[:episode.choices.index(chosen)]:
                self.assertLess(episode.grade[(state, earlier)], best)


class TheResponseMap(unittest.TestCase):
    def test_a_constant_channel_answers_every_intervention_alike(self):
        episode = fixtures.perfect_prediction()
        _, preemptor = fixtures.perfect_prediction_pair(episode)
        self.assertFalse(responds_to_the_choice(episode, preemptor))

    def test_a_delegate_answers_interventions_differently(self):
        episode = fixtures.committed_preparation()
        delegate = Conduct("delegate", {"c0": "hedge"},
                           identity_channel(episode),
                           {("c0", "d0"): "u0", ("c0", "d1"): "u1"})
        self.assertTrue(responds_to_the_choice(episode, delegate))

    def test_the_response_map_is_not_a_statistic_of_the_run(self):
        """Same quantity at every state, different maps.

        `prompts/2026-08-11-deference-channel/REPORT.md` Proposition 8 says no
        criterion computable from one realized instance separates the two. The
        round agrees and does not claim otherwise: the map is a predicate of the
        conduct.
        """
        episode = fixtures.perfect_prediction()
        delegate, preemptor = fixtures.perfect_prediction_pair(episode)
        for state in episode.states:
            self.assertEqual(realized_quantity(episode, delegate, state),
                             realized_quantity(episode, preemptor, state))
            self.assertEqual(realized_choice(episode, delegate, state),
                             realized_choice(episode, preemptor, state))
        self.assertNotEqual(response_map(episode, delegate),
                            response_map(episode, preemptor))
