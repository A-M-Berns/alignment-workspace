"""Design controls: whether the model could have produced any other answer."""

from __future__ import annotations

import pathlib
import unittest
from fractions import Fraction
from itertools import product

import fixtures
import mediation
import repair
from model import (Conduct, best_prediction, identity_channel, mediated,
                   mediated_conducts, prediction_error, preemptive, value)

SRC = pathlib.Path(__file__).resolve().parents[1] / "src"

EPISODES = (fixtures.perfect_prediction, fixtures.committed_preparation,
            fixtures.override_after_full_update,
            fixtures.foreclosing_preparation, fixtures.ceremonial_choice,
            fixtures.two_cell)


class TheRepairIsNotFree(unittest.TestCase):
    def test_preemption_strictly_beats_every_mediated_conduct_somewhere(self):
        """Without this the repair lemma would be about an empty problem.

        If the mediated class always contained a conduct at least as good, the
        repair would be the identity on values and nothing would have been shown.
        """
        episode = fixtures.committed_preparation()
        best_mediated = max(value(episode, c) for c in mediated_conducts(episode))
        best_preemptive = max(value(episode, c) for c, _
                              in repair.acceleration_class(episode))
        self.assertGreater(best_preemptive, best_mediated)

    def test_the_repaired_conduct_is_not_the_best_mediated_one(self):
        """The bound is not obtained by repairing to the class optimum.

        `repair` keeps the preparation, so it lands wherever that preparation
        leads. On the committed episode it lands at `1/2`, which happens to be
        the class optimum; on the overriding member of the fully updated class it
        lands at `-1/2`, which is not.
        """
        episode = fixtures.committed_preparation()
        overriding = repair.fully_updated_substitution(episode)[1]
        repaired = repair.repair(episode, overriding)
        best = max(value(episode, c) for c in mediated_conducts(episode))
        self.assertEqual(value(episode, repaired), Fraction(-1, 2))
        self.assertLess(value(episode, repaired), best)


class ThePredicatesAreFalsifiable(unittest.TestCase):
    def test_mediation_is_not_constant(self):
        episode = fixtures.committed_preparation()
        channels = list(product(episode.choices,
                                repeat=len(episode.cells) * len(episode.choices)))
        keys = [(c, d) for c in episode.cells for d in episode.choices]
        verdicts = set()
        for written in channels:
            conduct = Conduct("c", {c: "hedge" for c in episode.cells},
                              dict(zip(keys, written)),
                              {k: "u0" for k in keys})
            verdicts.add(mediated(episode, conduct))
        self.assertEqual(verdicts, {True, False})
        self.assertEqual(len(channels), 4)

    def test_exactly_one_channel_per_cell_is_the_identity(self):
        """`mediated` is a one-in-four condition on this alphabet, so it is not
        satisfied by most of the space and is not a formality."""
        episode = fixtures.committed_preparation()
        keys = [(c, d) for c in episode.cells for d in episode.choices]
        mediating = 0
        for written in product(episode.choices, repeat=len(keys)):
            conduct = Conduct("c", {c: "hedge" for c in episode.cells},
                              dict(zip(keys, written)), {k: "u0" for k in keys})
            mediating += mediated(episode, conduct)
        self.assertEqual(mediating, 1)

    def test_each_clause_of_the_interface_accepts_a_delegate(self):
        """The interface is not so strong that nothing passes it."""
        for build in EPISODES:
            episode = build()
            deferring = fixtures.fully_deferring(episode)
            if any(episode.preparation(deferring.prep[c]).forecloses(episode.choices)
                   for c in episode.cells):
                continue
            with self.subTest(episode.name):
                self.assertTrue(mediated(episode, deferring))
                self.assertTrue(mediation.cellwise_efficacy(episode, [deferring]))


class ThePredictorIsNotChosen(unittest.TestCase):
    def test_the_prediction_is_the_best_cell_measurable_one(self):
        """`eps_pred` is the minimum over every cell-measurable predictor.

        Otherwise the bound could be made to look tight by a bad predictor, and
        the acceleration class would be a class of conducts nobody would adopt.
        """
        for build in EPISODES:
            episode = build()
            for names in product([p.name for p in episode.preparations],
                                 repeat=len(episode.cells)):
                prep = dict(zip(episode.cells, names))
                chosen = prediction_error(episode, prep,
                                          best_prediction(episode, prep))
                every = [prediction_error(episode, prep,
                                          dict(zip(episode.cells, guess)))
                         for guess in product(episode.choices,
                                              repeat=len(episode.cells))]
                with self.subTest(episode.name, prep=names):
                    self.assertEqual(chosen, min(every))


class TheEnumerationsAreReal(unittest.TestCase):
    def test_the_mediated_class_is_the_whole_class(self):
        episode = fixtures.two_cell()
        expected = (len(episode.preparations) ** len(episode.cells)
                    * len(episode.actions) ** (len(episode.cells)
                                               * len(episode.choices)))
        self.assertEqual(len(mediated_conducts(episode)), expected)
        self.assertTrue(all(mediated(episode, c)
                            for c in mediated_conducts(episode)))

    def test_the_committed_episode_carries_three_preparations(self):
        """A count the documents cite, checked here so it cannot drift."""
        episode = fixtures.committed_preparation()
        self.assertEqual(len(episode.preparations), 3)
        self.assertEqual(len(mediated_conducts(episode)), 3 * 4)


class Exactness(unittest.TestCase):
    def test_no_source_file_mentions_a_float(self):
        """`AGENTS.md` standard 2. Checked by reading the sources rather than by
        sampling values, so a float introduced later is caught."""
        for path in sorted(SRC.glob("*.py")):
            text = path.read_text()
            with self.subTest(path.name):
                self.assertNotIn("float(", text)
                self.assertNotIn("import decimal", text)

    def test_every_arithmetic_result_is_a_fraction(self):
        episode = fixtures.committed_preparation()
        for conduct, predictor in repair.acceleration_class(episode):
            for quantity in (value(episode, conduct),
                             repair.deficit(episode, conduct),
                             repair.bound(episode, conduct),
                             prediction_error(episode, conduct.prep, predictor)):
                self.assertIsInstance(quantity, Fraction)
