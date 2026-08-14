from __future__ import annotations

import sys
import unittest
from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
PREP = HERE.parent / "2026-08-11-phi-regret-prep"
sys.path[:0] = [str(HERE / "src"), str(PREP)]

from src import experiments as ex
from src.model import GUARD_FOOTPRINT, reader_at
from src.replay import Comparator, replay

from online_interface import (
    PaddedRound,
    PreActionReader,
    available_actions,
    charge_vector,
    expected_loss,
    induced_action_map,
    pushforward,
    stationary_support_is_available,
)


class CausalCompilation(unittest.TestCase):

    def test_pre_action_reader_removes_current_transcript_response(self):
        experiment = ex.e3_lawful_one_shot()
        occasion = next(o for o in experiment.history.actual_occasions()
                        if o.occasion_id == "o:1")
        ordinary = reader_at(experiment.history, occasion.date, GUARD_FOOTPRINT)
        strict = PreActionReader(experiment.history, occasion.date, GUARD_FOOTPRINT)
        self.assertIsNotNone(ordinary.response(occasion.occasion_id))
        self.assertIsNone(strict.response(occasion.occasion_id))

    def test_canonical_repair_compiles_to_a_closed_action_map(self):
        experiment = ex.e3_lawful_one_shot()
        comparator = experiment.comparators[0]
        occasion = next(o for o in experiment.history.actual_occasions()
                        if o.occasion_id == "o:1")
        actions = available_actions(occasion)
        transform = induced_action_map(experiment.history, occasion, comparator, actions)
        self.assertEqual(set(transform), set(actions))
        self.assertTrue(set(transform.values()) <= set(actions))
        self.assertNotEqual(transform[experiment.history.responses[occasion.occasion_id]],
                            experiment.history.responses[occasion.occasion_id])

    def test_additive_compilation_matches_replay_without_coupling(self):
        experiment = ex.e3_lawful_one_shot()
        comparator = experiment.comparators[0]
        fired_before = False
        total = Q(0)
        for occasion in experiment.history.actual_occasions():
            actions = available_actions(occasion)
            transform = induced_action_map(experiment.history, occasion, comparator,
                                           actions, fired_before=fired_before)
            actual = experiment.history.responses[occasion.occasion_id]
            changed = transform[actual] != actual
            fired_before = fired_before or changed
            total += charge_vector(occasion, actions)[transform[actual]]
        self.assertFalse(experiment.history.accounting.suspends)
        self.assertEqual(total, replay(experiment.history, comparator).total_charge)

    def test_legality_is_invariant_to_tariff_changes(self):
        experiment = ex.e3_lawful_one_shot()
        comparator = experiment.comparators[0]
        occasion = next(o for o in experiment.history.actual_occasions()
                        if o.occasion_id == "o:1")
        actions = available_actions(occasion)
        first = induced_action_map(experiment.history, occasion, comparator, actions)
        changed_schedule = replace(occasion.schedule, default_tariff=Q(17),
                                   refusal_tariff=Q(23))
        changed_occasion = replace(occasion, schedule=changed_schedule)
        changed_occasions = tuple(changed_occasion if o.occasion_id == occasion.occasion_id else o
                                  for o in experiment.history.base_occasions)
        changed_history = replace(experiment.history, base_occasions=changed_occasions)
        second_actions = available_actions(changed_occasion)
        second = induced_action_map(changed_history, changed_occasion, comparator,
                                    second_actions)
        self.assertEqual(first, second)
        self.assertNotEqual(charge_vector(occasion, actions),
                            charge_vector(changed_occasion, second_actions))

    def test_tariff_is_not_exposed_through_callback_arguments(self):
        experiment = ex.e3_lawful_one_shot()
        template = experiment.comparators[0]
        occasion = next(o for o in experiment.history.actual_occasions()
                        if o.occasion_id == "o:1")

        def profit_guard(reader, occ, action):
            return occ.schedule.refusal_tariff > 0 and template.guard(reader, occ, action)

        seeking = Comparator("phi:tariff-seeking", profit_guard, template.propose)
        actions = available_actions(occasion)
        compiled = induced_action_map(experiment.history, occasion, seeking, actions)
        self.assertEqual(compiled, {action: action for action in actions})
        # The old raw interface does expose the tariff; the sealed adapter is
        # doing real work rather than testing an already-enforced property.
        raw = reader_at(experiment.history, occasion.date, GUARD_FOOTPRINT)
        actual = experiment.history.responses[occasion.occasion_id]
        self.assertTrue(profit_guard(raw, occasion, actual))

    def test_callback_closure_can_bypass_the_argument_seal(self):
        experiment = ex.e3_lawful_one_shot()
        template = experiment.comparators[0]
        occasion = next(o for o in experiment.history.actual_occasions()
                        if o.occasion_id == "o:1")

        def captured_guard(reader, sealed_occasion, action):
            return (occasion.schedule.refusal_tariff > 0
                    and template.guard(reader, sealed_occasion, action))

        captured = Comparator("phi:captured-tariff", captured_guard,
                              template.propose)
        actions = available_actions(occasion)
        transform = induced_action_map(experiment.history, occasion, captured,
                                       actions)
        actual = experiment.history.responses[occasion.occasion_id]
        self.assertNotEqual(transform[actual], actual)


class ChangingActionSets(unittest.TestCase):

    def setUp(self):
        self.padded = PaddedRound(
            actions=("a", "b", "c"), available=frozenset(("a", "b")),
            retract={"a": "a", "b": "b", "c": "a"},
            loss={"a": Q(1), "b": Q(2)})

    def test_raw_union_padding_creates_artificial_regret(self):
        local_loss = {"a": Q(1), "b": Q(2)}
        raw_padded_loss = {"a": Q(1), "b": Q(2), "c": Q(0)}
        self.assertEqual(min(local_loss.values()), Q(1))
        self.assertEqual(min(raw_padded_loss.values()), Q(0))

    def test_repository_response_union_grows_with_the_horizon(self):
        for horizon, expected in ((12, 41), (24, 77), (48, 149), (96, 293)):
            occasions = [ex.occasion(i) for i in range(horizon)]
            union = {action for occasion in occasions
                     for action in available_actions(occasion)}
            with self.subTest(horizon=horizon):
                self.assertEqual(len(union), expected)
                self.assertEqual(len(union), 3 * horizon + 5)

    def test_retraction_padding_preserves_actual_and_comparator_loss(self):
        local_map = {"a": "b", "b": "a"}
        compiled = self.padded.compile_map(local_map)
        distribution = {"a": Q(1, 3), "b": Q(2, 3), "c": Q(0)}
        padded_loss = {a: self.padded.padded_loss(a) for a in self.padded.actions}
        local_actual = expected_loss(distribution, {"a": Q(1), "b": Q(2), "c": Q(1)})
        encoded_actual = expected_loss(distribution, padded_loss)
        local_changed = expected_loss(pushforward(distribution, compiled), padded_loss)
        self.assertEqual(local_actual, encoded_actual)
        self.assertEqual(local_changed, Q(4, 3))

    def test_stationary_distribution_cannot_select_unavailable_actions(self):
        rows = {
            "a": {"a": Q(1, 2), "b": Q(1, 2)},
            "b": {"a": Q(1, 2), "b": Q(1, 2)},
            "c": {"a": Q(1, 2), "b": Q(1, 2)},
        }
        stationary = {"a": Q(1, 2), "b": Q(1, 2), "c": Q(0)}
        self.assertTrue(stationary_support_is_available(self.padded, stationary, rows))


if __name__ == "__main__":
    unittest.main()
