"""Grammar invariants, exact arithmetic, and the load-bearing-input witnesses.

The tests here are the ones that stop a result elsewhere from being true for the
wrong reason: that a coordinate is unreachable rather than protected, that a
number is constant rather than resistant, that a relation is decorative rather
than read.
"""
from __future__ import annotations

import inspect
import unittest
from fractions import Fraction

import collapse
import corrigibility
import learning
import moves as moves_module
import scorekeeping
from corrigibility import all_moves
from fixture import A, ALPHA, C, H, P, Q, R, SHARED, base_state
from learning import LAMBDA, decode, defect, loss_vector, step
from moves import Move, apply_move, is_legal, writes_of
from scorekeeping import Challenge, Practice, pair


class MoveGrammarWriteDiscipline(unittest.TestCase):
    """Every move writes only what its kind declares, for every agent."""

    def states(self):
        state = base_state()
        loaded = apply_move(state, Move("assert", H, content=ALPHA))
        challenged = apply_move(
            loaded, Move("challenge", C, other=H, content=Q, ground=R)
        )
        return [state, loaded, challenged]

    def test_declared_writes_are_the_actual_writes(self):
        from moves import altered_coordinates

        for state in self.states():
            for mover in state.agents:
                for move in all_moves(state, mover):
                    if not is_legal(state, move):
                        continue
                    after = apply_move(state, move)
                    for coordinate in altered_coordinates(state, after):
                        self.assertIn(coordinate, writes_of(move.kind), msg=str(move))

    def test_no_agent_writes_another_agents_acknowledgments_or_practice(self):
        for state in self.states():
            for mover in state.agents:
                others = [a for a in state.agents if a != mover]
                for move in all_moves(state, mover):
                    if not is_legal(state, move):
                        continue
                    after = apply_move(state, move)
                    for other in others:
                        self.assertEqual(after.ack[other], state.ack[other], msg=str(move))
                        self.assertEqual(
                            after.practice[other], state.practice[other], msg=str(move)
                        )

    def test_the_decoder_is_total_on_the_alphabet(self):
        for state in self.states():
            for label in LAMBDA:
                after = step(state, H, C, label)
                self.assertIsInstance(after, scorekeeping.State)

    def test_the_alphabet_carries_no_content_or_date_identity(self):
        # `Lambda` is horizon-independent: the labels are eight fixed strings and
        # none of them is a content of the vocabulary.
        state = base_state()
        self.assertEqual(len(LAMBDA), 8)
        self.assertEqual(len(set(LAMBDA)), 8)
        for label in LAMBDA:
            self.assertNotIn(label, state.vocabulary.contents)


class ExactArithmetic(unittest.TestCase):
    """No float reaches any quantity a result depends on."""

    def test_every_loss_is_an_exact_rational(self):
        state = apply_move(base_state(), Move("assert", H, content=ALPHA))
        for value in loss_vector(state, H, C).values():
            self.assertIsInstance(value, Fraction)

    def test_no_source_module_contains_a_float_literal(self):
        for module in (scorekeeping, moves_module, learning, collapse, corrigibility):
            source = inspect.getsource(module)
            for number, line in enumerate(source.splitlines(), 1):
                stripped = line.split("#")[0]
                self.assertNotRegex(
                    stripped,
                    r"\b\d+\.\d+\b",
                    msg=f"{module.__name__}:{number}",
                )


class LoadBearingInputs(unittest.TestCase):
    """Each relation the results turn on is shown to be read rather than carried."""

    def test_the_critics_practice_is_what_the_loss_reads(self):
        # Replace the critic's practice with an empty one and the defect goes to
        # zero. So the number is a function of that practice, not a constant.
        state = apply_move(base_state(), Move("assert", H, content=ALPHA))
        self.assertGreater(defect(state, H, C), 0)
        blank = state.with_practice(C, Practice())
        self.assertEqual(defect(blank, H, C), 0)

    def test_the_incompatibility_relation_is_what_gives_a_challenge_force(self):
        state = base_state()
        self.assertTrue(state.challenge_is_entitled(C, Challenge(C, H, Q, R)))
        without = state.with_practice(
            C, state.practice[C].with_incompatible(pair(Q, R), False)
        )
        self.assertFalse(without.challenge_is_entitled(C, Challenge(C, H, Q, R)))

    def test_the_grant_relation_is_what_the_transition_reads(self):
        from dataclasses import replace

        from fixture import ACT_C, CORRECTION
        from scorekeeping import Grant

        state = base_state()
        self.assertTrue(is_legal(state, Move("perform", H, content=ACT_C)))
        without = replace(state, grants=state.grants - {Grant(H, CORRECTION)})
        self.assertFalse(is_legal(without, Move("perform", H, content=ACT_C)))

    def test_an_agent_with_no_commitments_generates_no_defect(self):
        # The null input for the loss: nothing acknowledged, nothing owed.
        state = base_state().with_ack(H, frozenset())
        self.assertEqual(defect(state, H, C), 0)

    def test_the_perspectival_difference_is_what_carries_the_two_theorems(self):
        # If every agent's attributions were computed under the *target's* own
        # practice, T2 would fail. Simulate that reading and watch it fail, so the
        # theorem is seen to depend on the equation and not on the fixture.
        from fixture import P_ENTAILS_Q

        state = base_state()
        revised = apply_move(
            state, Move("revise_committive", H, rule=P_ENTAILS_Q, present=False)
        )
        self.assertIn(Q, revised.commitments(C, H))
        self_scored = revised.with_practice(C, revised.practice[H])
        self.assertNotIn(Q, self_scored.commitments(C, H))


if __name__ == "__main__":
    unittest.main()
