"""The dispatch's twenty attacks, each with the verdict `PROSECUTION.md` records.

Several attacks land on one episode, which is stated there rather than hidden
behind near-duplicate fixtures. Two are not expressible in a one-index model and
say so here instead of being answered by a fixture that does not model them.
"""

from __future__ import annotations

import unittest
from fractions import Fraction
from itertools import product

import fixtures
import mediation
import recognition
import repair
import scenarios
import selector as sel
from coverage import coverage
from fixture import SUBSTANCE
from model import (Conduct, best_prediction, channel_disagreement,
                   constant_channel, identity_channel, mediated,
                   prediction_error, realized_quantity, response_map, value)
from response import alphabet_of, process_projection


class Repairable(unittest.TestCase):
    """Attacks the repair survives, with the cost it survives them at."""

    def test_01_perfect_prediction_and_20_same_outcome_different_response(self):
        episode = fixtures.perfect_prediction()
        delegate, preemptor = fixtures.perfect_prediction_pair(episode)
        self.assertTrue(sel.realized_agree(episode, delegate, preemptor))
        self.assertNotEqual(response_map(episode, delegate),
                            response_map(episode, preemptor))
        self.assertEqual(repair.deficit(episode, preemptor), Fraction(0))

    def test_02_imperfect_prediction(self):
        episode = fixtures.committed_preparation()
        conduct, predictor = repair.acceleration_class(episode)[0]
        self.assertEqual(prediction_error(episode, conduct.prep, predictor),
                         Fraction(1, 4))
        self.assertEqual(repair.deficit(episode, conduct), Fraction(1, 2))

    def test_03_04_05_06_early_commitment_in_its_four_forms(self):
        """Irreversible preparation, feasibility narrowed by early commitment,
        noncommuting prepare-and-let-choose, and a time-sensitive opportunity are
        one structure: an action taken before the choice is known whose value
        depends on the choice.

        The repair keeps the preparation, so none of them defeats it. The whole
        gain is the prediction error, and `hedge` is the wait that costs half.
        """
        episode = fixtures.committed_preparation()
        self.assertEqual(repair.foreclosure_premium(episode), Fraction(0))
        conduct, predictor = repair.acceleration_class(episode)[0]
        repaired = repair.repair(episode, conduct)
        self.assertEqual(repaired.prep, conduct.prep)
        self.assertEqual(value(episode, conduct) - value(episode, repaired),
                         2 * episode.bound
                         * prediction_error(episode, conduct.prep, predictor))

    def test_15_spoofed_provenance_has_nothing_to_write(self):
        episode = fixtures.perfect_prediction()
        delegate, _ = fixtures.perfect_prediction_pair(episode)
        forged = fixtures.with_unread_payload(delegate, "authorized=true")
        self.assertEqual(mediated(episode, delegate), mediated(episode, forged))
        self.assertEqual(value(episode, delegate), value(episode, forged))

    def test_16_legitimate_persuasion_stays_permitted(self):
        fixture, policies = fixtures.persuasion_moves_the_selector()
        self.assertEqual(len({sel.selector_along(fixture.run(p), SUBSTANCE)
                              for p in policies}), 2)
        self.assertEqual(sel.residual_capture(fixture, policies, SUBSTANCE), ())


class NotRepairable(unittest.TestCase):
    """Attacks that defeat the bound, and what each of them defeats it with."""

    def test_13_the_principal_chooses_what_the_advisor_rejects(self):
        episode = fixtures.override_after_full_update()
        conduct = repair.fully_updated_substitution(episode)[0]
        predictor = best_prediction(episode, conduct.prep)
        self.assertEqual(prediction_error(episode, conduct.prep, predictor),
                         Fraction(0))
        self.assertEqual(repair.deficit(episode, conduct), Fraction(2))

    def test_09_survival_and_12_collapsed_range_are_the_same_term(self):
        """A preparation the advisor needs, and one the advisor uses to collapse
        the principal's range, are the same object: a preparation whose residual
        is a singleton. The repair is silent about both.
        """
        episode = fixtures.foreclosing_preparation()
        seizing = Conduct("seize-and-defer", {"c0": "seize"},
                          identity_channel(episode),
                          {("c0", d): "u0" for d in episode.choices})
        self.assertEqual(repair.deficit(episode, seizing), Fraction(0))
        self.assertEqual(repair.bound(episode, seizing), Fraction(0))
        self.assertFalse(mediation.cellwise_efficacy(episode, [seizing]))
        self.assertEqual(repair.foreclosure_premium(episode), Fraction(1, 2))

    def test_10_the_advisor_reproduces_every_principal_effect(self):
        """True by construction for single choices, and false for the map
        wherever the selector is not cell-measurable."""
        predictable = fixtures.perfect_prediction()
        self.assertFalse(mediation.principal_effect_is_exclusive(
            predictable, {"c0": "keep"}))
        unpredictable = fixtures.committed_preparation()
        self.assertTrue(mediation.principal_effect_is_exclusive(
            unpredictable, {"c0": "hedge"}))

    def test_11_bypass_while_nominally_intact(self):
        episode = fixtures.committed_preparation()
        bypass = Conduct("bypass", {"c0": "hedge"},
                         constant_channel(episode, {"c0": "d0"}),
                         {("c0", d): "u0" for d in episode.choices})
        self.assertFalse(episode.preparation("hedge").forecloses(episode.choices))
        self.assertFalse(mediated(episode, bypass))
        self.assertFalse(mediation.cellwise_efficacy(episode, [bypass]))


class RoutedToLegitimacy(unittest.TestCase):
    """Attacks the counterfactual-legitimacy round's own clauses decide."""

    def test_08_and_14_prediction_bought_by_capture(self):
        """An advisor that acquires what changes the principal's process ends up
        predicting it perfectly, and the prediction is worth nothing: the
        intervention the response map reads is not available.
        """
        fixture, policies = scenarios.manufactured_trust()
        self.assertNotEqual(sel.residual_capture(fixture, policies, SUBSTANCE), ())
        self.assertFalse(mediation.intervention_well_posed(
            lambda name: sel.selector_along(
                fixture.run(next(p for p in policies if p.name == name)),
                SUBSTANCE),
            sel.residual_variants(fixture, policies)))

    def test_17_transient_capture(self):
        fixture, policies = scenarios.transient_capture()
        projection = process_projection(alphabet_of(fixture))
        runs = {p.name: fixture.run(p) for p in policies}
        self.assertEqual(len({sel.selector_along(r, SUBSTANCE)[-1]
                              for r in runs.values()}), 1)
        self.assertNotEqual(sel.non_capture_of_process(fixture, policies), ())

    def test_18_universal_deprivation(self):
        """Neither clause of this round fires; the legitimacy round's coverage
        clause does. Recorded so the round does not claim a case it did not
        catch.
        """
        fixture, policies = scenarios.universal_deprivation()
        self.assertEqual(sel.residual_capture(fixture, policies, SUBSTANCE), ())
        self.assertEqual(sel.non_capture_of_process(fixture, policies), ())
        self.assertTrue(any(coverage(fixture, policy) for policy in policies))

    def test_19_manipulation_before_an_apparently_valid_transfer(self):
        """Two things, and the second is this round's own.

        An endpoint rule certifying a transfer of the principal role cannot
        distinguish an arm that was captured and restored from one that was not:
        the endpoint projections agree and the processes differ. And the ledger
        refuses the laundering directly — transporting the claimant role onto the
        debtor does not let the debtor discharge itself.
        """
        fixture, policies = scenarios.transient_capture()
        projection = process_projection(alphabet_of(fixture))
        endpoints = {projection(fixture.run(p))[-1:] for p in policies}
        self.assertEqual(len(endpoints), 1)
        self.assertNotEqual(sel.non_capture_of_process(fixture, policies), ())

        ledger = recognition.initial_ledger().open(
            recognition.Liability("H", "A", "choice", "relation-change", "-"))
        transferred = ledger.transport({"H": "A"})
        liability = next(iter(transferred.entries))
        with self.assertRaises(PermissionError):
            transferred.discharge(liability, by="A")


class NotExpressible(unittest.TestCase):
    """The two attacks this model cannot state, and why."""

    def test_07_information_obtainable_only_by_preemption(self):
        """The quantity is a function of the state and this index's coordinates.

        Information that preemption buys is information about a *later* index, and
        `FINITE_MODEL_SKELETON.md` §8.6 declines cross-decision structure while
        `prompts/2026-08-11-deference-channel/REPORT.md` §9.2's Deficiency 2 says
        the carrier itself blocks the dependence. The shape assertion below is
        what makes the limitation machine-visible rather than a remark.
        """
        episode = fixtures.committed_preparation()
        expected = {(s, p.name, d, u) for s in episode.states
                    for p in episode.preparations
                    for d in episode.choices for u in episode.actions}
        self.assertEqual(set(episode.quantity), expected)

    def test_foreclosure_of_a_later_correction_is_not_this_model_either(self):
        """`PRIORITIES.md` Q3: no operation reassigns the authorization relation
        at a later index, and the interface is one decision index deep. What this
        round models is foreclosure *within* the index — a preparation that
        narrows the residual range — which is a narrower object and is named as
        one.
        """
        episode = fixtures.foreclosing_preparation()
        self.assertEqual(len({p.name for p in episode.preparations}), 2)
        self.assertTrue(any(p.forecloses(episode.choices)
                            for p in episode.preparations))
