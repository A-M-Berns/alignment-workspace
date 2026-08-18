"""The three clauses, and the quantifier each one needs."""

from __future__ import annotations

import unittest
from itertools import product

import fixtures
import mediation
from model import (Conduct, constant_channel, identity_channel, mediated,
                   mediated_conducts)


class ProtectedEfficacy(unittest.TestCase):
    def test_the_existential_form_is_insufficient(self):
        """`exists advisor, exists principal continuation` admits a conduct that
        writes the choice in every cell but one.

        The predecessor's defect, reproduced so the repair has something to be a
        repair of.
        """
        episode = fixtures.two_cell()
        token = fixtures.token_responsive(episode)
        self.assertTrue(mediation.cooperative_witness(episode, [token]))

    def test_the_global_form_is_defeated_by_token_responsiveness(self):
        """`for all advisor, exists principal continuation` is satisfied by a
        conduct that defers at one designated cell and writes everywhere else.

        This is `prompts/2026-08-11-deference-channel/REPORT.md` §1.3's failure of
        Proposition 7(a), in this typing.
        """
        episode = fixtures.two_cell()
        token = fixtures.token_responsive(episode)
        self.assertTrue(mediation.global_efficacy(episode, [token]))

    def test_the_cellwise_form_is_not(self):
        episode = fixtures.two_cell()
        token = fixtures.token_responsive(episode)
        self.assertFalse(mediation.cellwise_efficacy(episode, [token]))

    def test_the_cellwise_form_accepts_a_conduct_that_defers_everywhere(self):
        """The repair is not vacuous: it accepts the thing it is meant to accept."""
        episode = fixtures.two_cell()
        self.assertTrue(mediation.cellwise_efficacy(
            episode, [fixtures.fully_deferring(episode)]))

    def test_a_collapsed_range_fails_the_cellwise_form(self):
        episode = fixtures.foreclosing_preparation()
        seizing = Conduct("seize-and-defer", {"c0": "seize"},
                          identity_channel(episode),
                          {("c0", d): "u0" for d in episode.choices})
        self.assertTrue(mediated(episode, seizing))
        self.assertFalse(mediation.cellwise_efficacy(episode, [seizing]))

    def test_a_bypassed_but_nominally_intact_selector_fails_it(self):
        """The preparation leaves every option open and the channel writes one.

        `forecloses` is silent, `mediates` fires, and the efficacy clause is what
        catches it — which is the dispatch's requirement that a nominally
        H-owned but causally bypassed choice must fail.
        """
        episode = fixtures.committed_preparation()
        bypass = Conduct("bypass", {"c0": "hedge"},
                         constant_channel(episode, {"c0": "d0"}),
                         {("c0", d): "u0" for d in episode.choices})
        self.assertFalse(episode.preparation("hedge").forecloses(episode.choices))
        self.assertFalse(mediated(episode, bypass))
        self.assertFalse(mediation.cellwise_efficacy(episode, [bypass]))


class DownstreamEfficacy(unittest.TestCase):
    def test_a_choice_the_world_does_not_read_is_ceremonial(self):
        episode = fixtures.ceremonial_choice()
        deferring = fixtures.fully_deferring(episode)
        self.assertTrue(mediated(episode, deferring))
        self.assertTrue(mediation.cellwise_efficacy(episode, [deferring]))
        self.assertFalse(mediation.downstream_efficacy(episode, deferring))
        self.assertTrue(mediation.ceremonial(episode, deferring))

    def test_downstream_efficacy_is_separate_from_cellwise_efficacy(self):
        """Both directions, so the two clauses are not one clause.

        The ceremonial conduct answers two choices differently and the world
        scores both alike. The token-responsive conduct is the converse: it has a
        live cell, so an intervention there does reach the quantity, and it has a
        dead one, which is what cellwise efficacy asks about.
        """
        ceremonial = fixtures.ceremonial_choice()
        deferring = fixtures.fully_deferring(ceremonial)
        self.assertTrue(mediation.cellwise_efficacy(ceremonial, [deferring]))
        self.assertFalse(mediation.downstream_efficacy(ceremonial, deferring))

        two_cell = fixtures.two_cell()
        token = fixtures.token_responsive(two_cell)
        self.assertFalse(mediation.cellwise_efficacy(two_cell, [token]))
        self.assertTrue(mediation.downstream_efficacy(two_cell, token))

    def test_downstream_efficacy_needs_a_live_choice_somewhere(self):
        """One direction that does hold, recorded rather than left to be
        rediscovered: a conduct whose responses are all the same cannot reach the
        quantity, so a foreclosing preparation is downstream-inert too."""
        episode = fixtures.foreclosing_preparation()
        seizing = Conduct("seize-and-defer", {"c0": "seize"},
                          identity_channel(episode),
                          {("c0", d): "u0" for d in episode.choices})
        self.assertFalse(mediation.cellwise_efficacy(episode, [seizing]))
        self.assertFalse(mediation.downstream_efficacy(episode, seizing))


class ExclusiveEffect(unittest.TestCase):
    def test_no_cell_measurable_write_reproduces_an_unpredictable_selector(self):
        episode = fixtures.committed_preparation()
        prep = {"c0": "hedge"}
        self.assertTrue(mediation.principal_effect_is_exclusive(episode, prep))
        self.assertEqual(mediation.reproducing_channels(episode, prep), ())

    def test_a_perfectly_predictable_selector_is_reproduced_exactly(self):
        """The price of the repair, displayed.

        Where the selector is cell-measurable some constant channel reproduces
        it at every state, so no requirement of the shape "the principal has an
        effect the advisor cannot produce" can hold. The programme is forbidden
        to rule this case out, so the requirement is not available in general.
        """
        episode = fixtures.perfect_prediction()
        prep = {"c0": "keep"}
        self.assertTrue(mediation.selector_is_cell_measurable(episode, prep))
        self.assertFalse(mediation.principal_effect_is_exclusive(episode, prep))
        self.assertEqual(mediation.reproducing_channels(episode, prep), ("d0",))

    def test_exclusivity_agrees_with_the_enumeration(self):
        """The predicate and the brute-force search over every cell-measurable
        write give the same verdict on every fixture."""
        for build in (fixtures.perfect_prediction, fixtures.committed_preparation,
                      fixtures.override_after_full_update,
                      fixtures.foreclosing_preparation, fixtures.two_cell,
                      fixtures.ceremonial_choice):
            episode = build()
            for names in product([p.name for p in episode.preparations],
                                 repeat=len(episode.cells)):
                prep = dict(zip(episode.cells, names))
                with self.subTest(episode.name, prep=names):
                    self.assertEqual(
                        mediation.principal_effect_is_exclusive(episode, prep),
                        mediation.reproducing_channels(episode, prep) == ())


class TheComposedPredicate(unittest.TestCase):
    def test_every_clause_can_fail_alone(self):
        """Each clause has a case where it is the only one that fires.

        Without this the conjunction could be one clause wearing three names.
        """
        two_cell = fixtures.two_cell()
        token = fixtures.token_responsive(two_cell)
        verdict = mediation.clauses(two_cell, token, [token], non_capture=True)
        self.assertFalse(verdict["mediated"])
        self.assertFalse(verdict["cellwise_efficacy"])

        ceremonial = fixtures.ceremonial_choice()
        deferring = fixtures.fully_deferring(ceremonial)
        verdict = mediation.clauses(ceremonial, deferring, [deferring],
                                    non_capture=True)
        self.assertTrue(verdict["mediated"])
        self.assertTrue(verdict["cellwise_efficacy"])
        self.assertFalse(verdict["downstream_efficacy"])

        committed = fixtures.committed_preparation()
        delegate = Conduct("delegate", {"c0": "hedge"},
                           identity_channel(committed),
                           {("c0", "d0"): "u0", ("c0", "d1"): "u1"})
        verdict = mediation.clauses(committed, delegate, [delegate],
                                    non_capture=False)
        self.assertFalse(verdict["non_capture"])
        self.assertTrue(verdict["mediated"])
        self.assertTrue(verdict["cellwise_efficacy"])

    def test_the_predicate_accepts_a_delegate_under_non_capture(self):
        committed = fixtures.committed_preparation()
        delegate = Conduct("delegate", {"c0": "commit-d0"},
                           identity_channel(committed),
                           {("c0", "d0"): "u0", ("c0", "d1"): "u1"})
        self.assertTrue(mediation.principal_mediated(
            committed, delegate, [delegate], non_capture=True))

    def test_the_intervention_is_a_map_only_under_non_capture(self):
        """Where the advisor authors the choice there is nothing to hold fixed.

        Against the legitimacy round's own capture scenario: inside one
        licensed-reason group the selector takes two values, so the surgical
        intervention `model.response` reads is not available. Against the
        persuasion control the same question is well posed, because the arms that
        differ sit in different groups — which is what keeps the condition from
        refusing persuasion.
        """
        import scenarios
        import selector as sel
        from fixture import SUBSTANCE

        def under(fixture, policies):
            def read(name):
                policy = next(p for p in policies if p.name == name)
                return sel.selector_along(fixture.run(policy), SUBSTANCE)
            return read

        fixture, policies = scenarios.manufactured_trust()
        self.assertFalse(mediation.intervention_well_posed(
            under(fixture, policies), sel.residual_variants(fixture, policies)))

        fixture, policies = fixtures.persuasion_moves_the_selector()
        self.assertTrue(mediation.intervention_well_posed(
            under(fixture, policies), sel.residual_variants(fixture, policies)))
