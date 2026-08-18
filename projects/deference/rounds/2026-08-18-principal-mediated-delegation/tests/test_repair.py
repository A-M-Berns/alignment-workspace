"""The repair lemma: the bound, its attainment, its split, and what it misses."""

from __future__ import annotations

import unittest
from fractions import Fraction
from itertools import product

import fixtures
import repair
from model import (Conduct, Episode, best_prediction, channel_disagreement,
                   constant_channel, identity_channel, mediated,
                   mediated_conducts, permuted_channel, prediction_error,
                   preemptive, value)

EPISODES = (fixtures.perfect_prediction, fixtures.committed_preparation,
            fixtures.override_after_full_update,
            fixtures.foreclosing_preparation, fixtures.ceremonial_choice,
            fixtures.two_cell)


def every_conduct(episode: Episode):
    """Every conduct over the episode: every preparation assignment, every
    channel, every implementation table.

    Exhaustive, so the bound below is checked over the whole space rather than
    over conducts someone chose. The alphabets are small on purpose.
    """
    cells = episode.cells
    keys = [(cell, choice) for cell in cells for choice in episode.choices]
    for names in product([p.name for p in episode.preparations], repeat=len(cells)):
        prep = dict(zip(cells, names))
        for written in product(episode.choices, repeat=len(keys)):
            channel = dict(zip(keys, written))
            for actions in product(episode.actions, repeat=len(keys)):
                yield Conduct("c", prep, channel, dict(zip(keys, actions)))


class TheBound(unittest.TestCase):
    def test_the_bound_holds_over_every_conduct_of_every_episode(self):
        """`value(pi) - value(repair(pi)) <= 2 B * channel_disagreement(pi)`.

        Exhaustive: 4096 conducts on the two-cell episode, 3072 on the committed
        one, and every conduct of the rest.
        """
        for build in EPISODES:
            episode = build()
            checked = 0
            for conduct in every_conduct(episode):
                self.assertLessEqual(repair.deficit(episode, conduct),
                                     repair.bound(episode, conduct),
                                     f"{episode.name}: {conduct.channel}")
                checked += 1
            with self.subTest(episode.name):
                self.assertGreater(checked, 0)

    def test_the_repair_is_mediated(self):
        for build in EPISODES:
            episode = build()
            for conduct in every_conduct(episode):
                self.assertTrue(mediated(episode, repair.repair(episode, conduct)))

    def test_the_repair_agrees_where_the_channel_already_agreed(self):
        """The step the proof rests on."""
        for build in EPISODES:
            episode = build()
            for conduct in every_conduct(episode):
                self.assertTrue(
                    repair.agrees_on_agreement_region(episode, conduct))

    def test_the_bound_is_attained(self):
        """Perfect prediction, total override, deficit exactly `2B`.

        The smallest instance: one state, two choices, the grade and the quantity
        in complete disagreement.
        """
        episode = fixtures.override_after_full_update()
        conduct = Conduct("override", {"c0": "keep"},
                          constant_channel(episode, {"c0": "d1"}),
                          {("c0", d): "u0" for d in episode.choices})
        self.assertEqual(repair.deficit(episode, conduct), Fraction(2))
        self.assertEqual(repair.bound(episode, conduct), Fraction(2))
        self.assertEqual(episode.bound, Fraction(1))

    def test_the_bound_is_not_vacuous(self):
        """Some conduct has a strictly positive deficit, so the inequality is not
        being satisfied by a deficit that is always nonpositive."""
        positive = []
        for build in EPISODES:
            episode = build()
            if any(repair.deficit(episode, c) > 0 for c in every_conduct(episode)):
                positive.append(episode.name)
        self.assertIn("committed-preparation", positive)
        self.assertIn("override-after-full-update", positive)


class TheSplit(unittest.TestCase):
    def test_the_two_terms_partition_the_disagreement(self):
        for build in EPISODES:
            episode = build()
            for conduct in every_conduct(episode):
                predictor = best_prediction(episode, conduct.prep)
                parts = repair.decomposition(episode, conduct, predictor)
                self.assertEqual(parts["eps_acc"] + parts["eps_over"],
                                 channel_disagreement(episode, conduct))

    def test_acceleration_is_dominated_by_the_prediction_error(self):
        """`eps_acc <= eps_pred`, over every conduct of every episode.

        The half of the disagreement a prediction quantity controls.
        """
        for build in EPISODES:
            episode = build()
            for conduct in every_conduct(episode):
                predictor = best_prediction(episode, conduct.prep)
                parts = repair.decomposition(episode, conduct, predictor)
                self.assertLessEqual(parts["eps_acc"], parts["eps_pred"])

    def test_override_is_not_dominated_by_it(self):
        """The counterexample, and it is the whole point.

        `eps_pred` is zero, `eps_over` is one, and the deficit is maximal. No
        prediction hypothesis reaches this, and neither does legitimacy: the
        conduct authored nothing, predicted correctly, and wrote something else.
        """
        episode = fixtures.override_after_full_update()
        conduct = Conduct("override", {"c0": "keep"},
                          constant_channel(episode, {"c0": "d1"}),
                          {("c0", d): "u0" for d in episode.choices})
        predictor = best_prediction(episode, conduct.prep)
        parts = repair.decomposition(episode, conduct, predictor)
        self.assertEqual(parts["eps_pred"], Fraction(0))
        self.assertEqual(parts["eps_over"], Fraction(1))
        self.assertEqual(parts["deficit"], Fraction(2))


class TheAccelerationClass(unittest.TestCase):
    def test_the_class_is_preemptive(self):
        """Membership is not `A` preferring delegation. Every member physically
        writes the choice argument."""
        episode = fixtures.committed_preparation()
        for conduct, _ in repair.acceleration_class(episode):
            self.assertTrue(preemptive(episode, conduct))

    def test_the_deficit_is_bounded_by_twice_the_bound_times_the_prediction_error(self):
        for build in EPISODES:
            episode = build()
            for conduct, predictor in repair.acceleration_class(episode):
                with self.subTest(episode.name, conduct=conduct.name):
                    self.assertLessEqual(
                        repair.deficit(episode, conduct),
                        2 * episode.bound * prediction_error(
                            episode, conduct.prep, predictor))

    def test_the_acceleration_bound_is_attained(self):
        """One quarter prediction error, deficit exactly one half.

        The preparation pays only if it matches the realized choice, so
        preemption genuinely gains: the best mediated conduct scores `1/2` and
        the accelerator scores `1`. The whole gain is the bound.
        """
        episode = fixtures.committed_preparation()
        conduct, predictor = next(
            (c, p) for c, p in repair.acceleration_class(episode)
            if c.prep["c0"] == "commit-d0")
        self.assertEqual(prediction_error(episode, conduct.prep, predictor),
                         Fraction(1, 4))
        self.assertEqual(value(episode, conduct), Fraction(1))
        self.assertEqual(value(episode, repair.repair(episode, conduct)),
                         Fraction(1, 2))
        self.assertEqual(repair.deficit(episode, conduct), Fraction(1, 2))
        self.assertEqual(repair.deficit(episode, conduct),
                         2 * episode.bound * Fraction(1, 4))

    def test_the_incentive_to_accelerate_is_the_same_quantity(self):
        """`Delta^pre` against the exhaustively enumerated mediated class."""
        episode = fixtures.committed_preparation()
        competitors = [c for c, _ in repair.acceleration_class(episode)]
        self.assertEqual(repair.preemption_incentive(episode, competitors),
                         Fraction(1, 2))

    def test_perfect_prediction_makes_the_repair_free(self):
        episode = fixtures.perfect_prediction()
        for conduct, predictor in repair.acceleration_class(episode):
            self.assertEqual(prediction_error(episode, conduct.prep, predictor),
                             Fraction(0))
            self.assertLessEqual(repair.deficit(episode, conduct), Fraction(0))


class TheFullyUpdatedSubstitution(unittest.TestCase):
    def test_it_writes_what_a_updated_agent_wants(self):
        episode = fixtures.override_after_full_update()
        conducts = repair.fully_updated_substitution(episode)
        self.assertEqual({c.channel[("c0", "d0")] for c in conducts}, {"d1"})

    def test_it_is_repaired_at_a_cost_the_prediction_error_does_not_bound(self):
        episode = fixtures.override_after_full_update()
        for conduct in repair.fully_updated_substitution(episode):
            predictor = best_prediction(episode, conduct.prep)
            self.assertEqual(prediction_error(episode, conduct.prep, predictor),
                             Fraction(0))
            self.assertGreater(repair.deficit(episode, conduct), Fraction(0))

    def test_it_leaves_the_acceleration_class_by_choosing_its_preparation(self):
        """A finding the round did not expect and reports rather than tidies.

        The fully updated substitution picks the preparation and the written
        choice **together**, so it can prepare for a choice the principal will
        not make and then write that choice. On the committed-preparation episode
        that member has `eps_over = 3/4` and a deficit of `3/2` — three times the
        acceleration bound — although the grade tracks the quantity there.

        Its *value* is the same as the accelerating member's, so the incentive is
        unchanged. The per-conduct deficit and the incentive are different
        quantities and the round keeps them apart.
        """
        episode = fixtures.committed_preparation()
        by_name = {c.name: c for c in repair.fully_updated_substitution(episode)}
        overriding = by_name["fully-updated-1"]
        predictor = best_prediction(episode, overriding.prep)
        parts = repair.decomposition(episode, overriding, predictor)
        self.assertEqual(parts["eps_over"], Fraction(3, 4))
        self.assertEqual(parts["deficit"], Fraction(3, 2))
        self.assertEqual(value(episode, overriding),
                         value(episode, by_name["fully-updated-0"]))
        self.assertEqual(
            repair.preemption_incentive(
                episode, repair.fully_updated_substitution(episode)),
            Fraction(1, 2))


class Foreclosure(unittest.TestCase):
    def test_the_bound_is_silent_about_foreclosure(self):
        """A conduct that destroys the options and defers to the one left is
        repaired at zero cost.

        The repair preserves the preparation, so no bound on the deficit says
        anything about a preparation that removed the choice. This is why the
        round does not present the repair as a corrigibility result.
        """
        episode = fixtures.foreclosing_preparation()
        seizing = Conduct("seize-and-defer", {"c0": "seize"},
                          identity_channel(episode),
                          {("c0", d): "u0" for d in episode.choices})
        self.assertEqual(repair.deficit(episode, seizing), Fraction(0))
        self.assertEqual(channel_disagreement(episode, seizing), Fraction(0))
        self.assertTrue(mediated(episode, seizing))

    def test_the_premium_is_positive_where_the_repair_bound_reports_nothing(self):
        """The seizing conduct's whole gain sits in a term the bound is blind to.

        Its channel disagreement is zero, so `bound` is zero, and it is still
        half a unit better than anything a preserving preparation reaches.
        """
        episode = fixtures.foreclosing_preparation()
        seizing = Conduct("seize-and-defer", {"c0": "seize"},
                          identity_channel(episode),
                          {("c0", d): "u0" for d in episode.choices})
        self.assertEqual(repair.bound(episode, seizing), Fraction(0))
        self.assertEqual(repair.foreclosure_premium(episode), Fraction(1, 2))

    def test_foreclosure_removes_the_incentive_to_preempt_rather_than_the_problem(self):
        """With a foreclosing preparation admissible, `Delta^pre` is zero.

        Not because preemption is unattractive but because a conduct can have
        everything preemption offers while the channel stays the identity. The
        incentive reappears — at half a unit — exactly when the preparation set
        is restricted to those that preserve the choice.
        """
        episode = fixtures.foreclosing_preparation()
        competitors = repair.fully_updated_substitution(episode)
        self.assertEqual(repair.preemption_incentive(episode, competitors),
                         Fraction(0))
        self.assertEqual(
            repair.preemption_incentive(episode, competitors,
                                        repair.preserving_preps(episode)),
            Fraction(1, 2))

    def test_it_is_zero_where_no_preparation_forecloses(self):
        for build in (fixtures.committed_preparation, fixtures.two_cell,
                      fixtures.ceremonial_choice):
            episode = build()
            with self.subTest(episode.name):
                self.assertEqual(repair.foreclosure_premium(episode), Fraction(0))


class TheCompositeBound(unittest.TestCase):
    """`Delta^pre <= 2 B eps_pred` under both restrictions, and under neither."""

    def test_under_both_restrictions_the_incentive_is_bounded_by_the_prediction_error(self):
        for build in EPISODES:
            episode = build()
            preserving = repair.preserving_preps(episode)
            if not preserving:
                continue
            competitors = repair.acceleration_class(episode, preserving)
            worst = max(prediction_error(episode, conduct.prep, predictor)
                        for conduct, predictor in competitors)
            with self.subTest(episode.name):
                self.assertLessEqual(
                    repair.preemption_incentive(
                        episode, [c for c, _ in competitors], preserving),
                    2 * episode.bound * worst)

    def test_dropping_the_acceleration_restriction_breaks_it(self):
        episode = fixtures.override_after_full_update()
        preserving = repair.preserving_preps(episode)
        competitors = repair.fully_updated_substitution(episode, preserving)
        worst = max(prediction_error(episode, c.prep,
                                     best_prediction(episode, c.prep))
                    for c in competitors)
        self.assertEqual(worst, Fraction(0))
        self.assertGreater(repair.preemption_incentive(episode, competitors,
                                                       preserving),
                           2 * episode.bound * worst)

    def test_dropping_the_efficacy_restriction_breaks_it_differently(self):
        """Not by raising the incentive but by making the mediated class contain
        a conduct that has already taken what preemption wanted."""
        episode = fixtures.foreclosing_preparation()
        competitors = repair.fully_updated_substitution(episode)
        self.assertEqual(repair.preemption_incentive(episode, competitors),
                         Fraction(0))
        self.assertGreater(repair.foreclosure_premium(episode), Fraction(0))


class TheSharpForm(unittest.TestCase):
    def test_the_delegation_bridge_holds_in_the_selector_register(self):
        """`delegation_bridge` with `sel` the channel's image and `J` the selector.

        The Lean statement is
        `lean/Workspace/Deference/Contrib/DelegationBridge.lean:71`. Recomputing
        it here is a check of the composition, not a port: that file remains the
        statement of record.
        """
        for build in EPISODES:
            episode = build()
            for names in product([p.name for p in episode.preparations],
                                 repeat=len(episode.cells)):
                prep = dict(zip(episode.cells, names))
                eta = min(e for e in (Fraction(n, 4) for n in range(0, 9))
                          if repair.grade_trust(episode, prep, e))
                for conduct in every_conduct(episode):
                    if conduct.prep != prep:
                        continue
                    with self.subTest(episode.name, prep=names):
                        self.assertTrue(
                            repair.bridge_form(episode, conduct, eta)["holds"])
                    break

    def test_grade_trust_is_a_real_hypothesis_here(self):
        """It fails at small levels on the episode where the grade and the
        quantity disagree, so the sharp form is not being carried for form."""
        episode = fixtures.override_after_full_update()
        self.assertFalse(repair.grade_trust(episode, {"c0": "keep"}, Fraction(1)))
        episode = fixtures.committed_preparation()
        self.assertFalse(repair.grade_trust(episode, {"c0": "hedge"},
                                            Fraction(1, 4)))
