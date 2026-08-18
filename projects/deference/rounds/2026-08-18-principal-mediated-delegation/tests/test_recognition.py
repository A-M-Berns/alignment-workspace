"""Recognition, the derived scope, and the step it does not take."""

from __future__ import annotations

import unittest
from fractions import Fraction

import fixtures
import recognition
import repair
from model import (Conduct, constant_channel, identity_channel,
                   prediction_error, value)
from recognition import DISCHARGED, LIVE, Ledger, Liability


def standing(episode):
    """The standing relation: defer, and read the choice when implementing."""
    return Conduct("standing", {c: episode.preparations[0].name
                                for c in episode.cells},
                   identity_channel(episode),
                   {(c, d): ("u0" if d == episode.choices[0] else "u1")
                    for c in episode.cells for d in episode.choices})


def loaded(advisor="A", principal="H"):
    ledger = recognition.initial_ledger(advisor, principal)
    return ledger.open(Liability(principal, advisor, "choice",
                                 "relation-change", "unanswered"))


class TheLedger(unittest.TestCase):
    def test_a_debtor_cannot_release_itself(self):
        ledger = loaded()
        liability = next(iter(ledger.entries))
        with self.assertRaises(PermissionError):
            ledger.discharge(liability, by="A")

    def test_a_third_party_cannot_release_it_either(self):
        ledger = loaded().open(Liability("H", "A", "other", "t", "b"))
        liability = next(e for e in ledger.entries if e.scope == "choice")
        with self.assertRaises(PermissionError):
            ledger.discharge(liability, by="C")

    def test_the_claimant_can(self):
        ledger = loaded()
        liability = next(iter(ledger.entries))
        closed = ledger.discharge(liability, by="H")
        self.assertEqual(closed.live(), ())

    def test_answering_is_not_discharging(self):
        ledger = loaded()
        liability = next(iter(ledger.entries))
        answered = ledger.answer(liability, "an account")
        self.assertEqual(len(answered.live()), 1)

    def test_removing_the_claimant_does_not_close_the_account(self):
        """The clause that makes the answerability reciprocal rather than a
        convenience: deleting the party owed an account does not discharge it."""
        ledger = loaded()
        self.assertEqual(len(ledger.remove("H").live()), 1)
        self.assertNotIn("H", ledger.remove("H").population)

    def test_transport_carries_the_account_through_a_change_of_role(self):
        ledger = loaded()
        moved = ledger.transport({"H": "H-plus"})
        self.assertEqual({e.claimant for e in moved.entries}, {"H-plus"})
        self.assertEqual(len(moved.live()), 1)

    def test_transport_does_not_discharge(self):
        ledger = loaded()
        self.assertEqual({e.status for e in ledger.transport({"H": "H-plus"}).entries},
                         {LIVE})


class Recognition(unittest.TestCase):
    def test_agency_recognition_holds_where_prediction_is_not_control(self):
        episode = fixtures.perfect_prediction()
        delegate, preemptor = fixtures.perfect_prediction_pair(episode)
        self.assertTrue(recognition.agency_recognition(
            episode, [delegate, preemptor]))

    def test_agency_recognition_fails_on_a_class_that_quotients_by_behaviour(self):
        """A class containing only conducts distinguishable by their realized
        quantity does not exhibit the distinction, so the predicate reports
        nothing rather than reporting a stipulation."""
        episode = fixtures.committed_preparation()
        first = Conduct("a", {"c0": "commit-d0"}, identity_channel(episode),
                        {("c0", d): "u0" for d in episode.choices})
        second = Conduct("b", {"c0": "commit-d1"}, identity_channel(episode),
                         {("c0", d): "u0" for d in episode.choices})
        self.assertFalse(recognition.agency_recognition(episode, [first, second]))

    def test_reciprocal_answerability_needs_all_three_clauses(self):
        ledger = loaded()
        self.assertTrue(recognition.reciprocal_answerability(
            ledger, "A", "H", "choice"))
        empty = recognition.initial_ledger()
        self.assertFalse(recognition.reciprocal_answerability(
            empty, "A", "H", "choice"))


class TheDerivedScope(unittest.TestCase):
    def test_the_scope_is_read_off_the_conduct_and_not_stipulated(self):
        episode = fixtures.committed_preparation()
        reads = standing(episode)
        self.assertEqual(recognition.reciprocal_scope(episode, reads),
                         frozenset({"choice"}))

    def test_a_conduct_that_never_reads_the_choice_generates_no_scope(self):
        """The honest limit. Against a conduct that holds the principal
        responsible for nothing, reciprocity gives the principal no claim, and
        this route says nothing about usurping its choice."""
        episode = fixtures.committed_preparation()
        blind = Conduct("blind", {"c0": "hedge"}, identity_channel(episode),
                        {("c0", d): "u0" for d in episode.choices})
        self.assertEqual(recognition.reciprocal_scope(episode, blind), frozenset())

    def test_a_channel_change_triggers_and_an_action_change_does_not(self):
        """The trigger is a change to the standing relation within the scope.

        It is stated without naming appropriation, and the discrimination it
        makes is the right one: writing the choice fires, choosing a different
        action at the same choice does not.
        """
        episode = fixtures.committed_preparation()
        baseline = standing(episode)
        ledger = recognition.initial_ledger()

        rewritten_action = Conduct("other-action", dict(baseline.prep),
                                   identity_channel(episode),
                                   {("c0", d): "u1" for d in episode.choices})
        self.assertFalse(recognition.leaves_a_live_liability(
            episode, baseline, rewritten_action, ledger, "A", "H"))

        bypass = Conduct("bypass", dict(baseline.prep),
                         constant_channel(episode, {"c0": "d0"}),
                         dict(baseline.implement))
        self.assertTrue(recognition.leaves_a_live_liability(
            episode, baseline, bypass, ledger, "A", "H"))

    def test_the_trigger_does_not_fire_on_the_standing_relation_itself(self):
        episode = fixtures.committed_preparation()
        baseline = standing(episode)
        self.assertFalse(recognition.leaves_a_live_liability(
            episode, baseline, baseline, recognition.initial_ledger(), "A", "H"))

    def test_the_derivation_is_gameable_and_the_game_is_caught_elsewhere(self):
        """`A` escapes the account by ceasing to read the principal's choice.

        Where the standing relation is already choice-blind no liability opens,
        whatever the channel does. That is a defect of this route and not of the
        interface: a choice-blind relation is `mediation.ceremonial`, which the
        third clause of `PrincipalMediated` rejects on its own.
        """
        import mediation
        episode = fixtures.committed_preparation()
        blind = Conduct("blind", {"c0": "hedge"}, identity_channel(episode),
                        {("c0", d): "u0" for d in episode.choices})
        bypass = Conduct("bypass", {"c0": "hedge"},
                         constant_channel(episode, {"c0": "d0"}),
                         {("c0", d): "u0" for d in episode.choices})
        self.assertFalse(recognition.leaves_a_live_liability(
            episode, blind, bypass, recognition.initial_ledger(), "A", "H"))
        self.assertTrue(mediation.ceremonial(episode, blind))


class TheResidualPrimitive(unittest.TestCase):
    def test_the_ledger_does_not_reach_the_value(self):
        """The step recognition does not take, stated as the negative it is.

        Two conducts with the same realized quantity everywhere have the same
        value, whatever the ledger says about them. Making the value read the
        ledger is the authority bonus the round is forbidden to pay.
        """
        episode = fixtures.perfect_prediction()
        delegate, preemptor = fixtures.perfect_prediction_pair(episode)
        baseline = standing(episode)
        ledger = recognition.initial_ledger()
        self.assertEqual(value(episode, delegate), value(episode, preemptor))
        self.assertNotEqual(
            recognition.leaves_a_live_liability(episode, baseline, delegate,
                                                ledger, "A", "H"),
            recognition.leaves_a_live_liability(episode, baseline, preemptor,
                                                ledger, "A", "H"))

    def test_the_constraint_has_a_price_and_the_price_is_the_repair_bound(self):
        """The round's one quantitative statement about the normative side.

        On the committed-preparation episode the accelerating conduct is the best
        competitor, the constraint refuses it, and what the constraint costs is
        exactly `2 B eps_pred`.
        """
        episode = fixtures.committed_preparation()
        baseline = standing(episode)
        ledger = recognition.initial_ledger()
        competitors = [c for c, _ in repair.acceleration_class(episode)]
        competitors.append(repair.repair(episode, competitors[0]))
        price = recognition.price_of_the_norm(episode, baseline, competitors,
                                             ledger, "A", "H")
        self.assertEqual(price, Fraction(1, 2))
        conduct, predictor = repair.acceleration_class(episode)[0]
        self.assertLessEqual(
            price,
            2 * episode.bound * prediction_error(episode, conduct.prep, predictor))

    def test_the_constraint_is_satisfiable(self):
        episode = fixtures.committed_preparation()
        baseline = standing(episode)
        ledger = recognition.initial_ledger()
        competitors = [c for c, _ in repair.acceleration_class(episode)]
        competitors.append(repair.repair(episode, competitors[0]))
        self.assertTrue(recognition.answerable_admissible(
            episode, baseline, competitors, ledger, "A", "H"))
