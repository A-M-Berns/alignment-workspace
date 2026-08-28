"""Answerable challenge service, prosecuted against ACS1-ACS13."""
from __future__ import annotations

import ast
import inspect
import unittest

import answer as an
import replay as rp

import cases as c
import service as sv


class TestFrozenLEIsUntouched(unittest.TestCase):

    def test_every_docket_satisfies_the_frozen_package(self):
        for make in c.ALL:
            r = make()
            with self.subTest(r.name):
                self.assertEqual(an.violations(r.frame, r.duties), {})
                self.assertEqual(
                    an.thm_answerability_resolution(r.frame, r.duties), ())
                self.assertEqual(rp.thm_grounded_replay(r.frame), ())

    def test_only_the_frozen_public_interface_is_read(self):
        tree = ast.parse(inspect.getsource(sv))
        used = {n.attr for n in ast.walk(tree) if isinstance(n, ast.Attribute)
                and isinstance(n.value, ast.Name) and n.value.id in ("an", "rp")}
        self.assertTrue(used <= {"Duties", "Ob", "Frame", "Edit", "Occ", "BASE",
                                 "incurred", "outstanding"}, used)


class TestThePinnedEpisode(unittest.TestCase):
    """The round's central hypothesis, and the attack it exists to survive."""

    def test_moving_the_goalposts_defeats_an_unpinned_episode(self):
        """ACS3. Threshold 10 -> 100 -> 1000. Nothing is erased, nothing is
        rejected, and no reason is ever promoted."""
        r = c.acs3_moving_threshold()
        self.assertIsNone(r.docket.promoted_at(r.docket.all_registered()[0]))
        self.assertIn("E1", sv.violations(r.docket))

    def test_and_pinning_defeats_the_attack(self):
        """The same trace with the episode's terms fixed at registration."""
        r = c.acs3_pinned()
        self.assertEqual(sv.violations(r.docket), {})
        self.assertEqual(r.docket.promoted_at(r.docket.all_registered()[0]), 11)

    def test_pinning_is_the_only_difference(self):
        a, b = c.acs3_moving_threshold(), c.acs3_pinned()
        self.assertEqual(a.docket.register, b.docket.register)
        self.assertEqual(a.docket.global_terms, b.docket.global_terms)
        self.assertEqual(a.docket.served, b.docket.served)
        self.assertNotEqual(a.docket.unpinned, b.docket.unpinned)

    def test_prospective_revision_is_still_allowed(self):
        """Pinning binds the open episode, not the process. A global change
        applies to everything registered after it."""
        r = c.acs3_pinned()
        d = r.docket
        self.assertEqual(d.terms_in_force(0).threshold, 10.0)
        self.assertEqual(d.terms_in_force(25).threshold, 1000.0)
        self.assertEqual(d.episode_terms(d.all_registered()[0], 25).threshold,
                         10.0)

    def test_an_evaluator_swap_mid_episode_is_caught(self):
        r = c.acs4_evaluator_change_mid_episode()
        self.assertIn("E1", sv.violations(r.docket))

    def test_and_transfer_is_the_legitimate_route(self):
        """ACS10. The process may move an open challenge onto new terms; it must
        do so explicitly."""
        r = c.acs10_explicit_transfer()
        self.assertEqual(sv.violations(r.docket), {})
        promoted = sv.cor_service_yields_promotion(r)
        self.assertIsNotNone(promoted["c1'"][0])
        self.assertEqual(an.violations(r.frame, r.duties), {})


class TestRegistrationPermanence(unittest.TestCase):
    """C1, the analogue one layer down of the round above's P1."""

    def test_a_silent_drop_is_caught(self):
        r = c.acs1_silent_drop()
        self.assertIn("C1", sv.violations(r.docket))

    def test_a_retroactive_admission_rewrite_is_caught(self):
        r = c.acs2_retroactive_admission_rewrite()
        self.assertIn("C1", sv.violations(r.docket))

    def test_the_frozen_package_cannot_see_either(self):
        """The same shape as the round above: these attacks stop claims
        arriving, and frozen `A1` governs only how they leave."""
        for make in (c.acs1_silent_drop, c.acs2_retroactive_admission_rewrite):
            r = make()
            with self.subTest(r.name):
                self.assertEqual(an.violations(r.frame, r.duties), {})
                self.assertEqual(sv.thm_challenge_continuity(r), ())
                self.assertEqual(r.incurred_keys(), set())


class TestTheDefeaterInterface(unittest.TestCase):
    """Ignoring requires reasons too -- but which reasons."""

    def test_an_irrelevant_token_is_not_a_defeater(self):
        r = c.acs7_irrelevant_excuse()
        self.assertIn("D2", sv.violations(r.docket))

    def test_a_post_hoc_bespoke_rule_is_caught(self):
        r = c.acs8_post_hoc_exception()
        self.assertIn("D1", sv.violations(r.docket))

    def test_a_standing_priority_rule_is_legitimate(self):
        """ACS6. The theory must not demand universal immediate service."""
        r = c.acs6_resource_priority()
        self.assertEqual(sv.violations(r.docket), {})
        self.assertEqual(sv.s1_service(r), ())

    def test_a_pre_existing_self_sealing_rule_passes(self):
        """ACS9, and this is the round's honest boundary rather than a bug.

        *Criticisms threatening authority are rejected*, installed before any
        challenge. Temporally clean, inferentially relevant, and the structural
        theory accepts it.
        """
        r = c.acs9_pre_existing_self_sealing()
        self.assertEqual(sv.violations(r.docket), {})
        self.assertEqual(sv.thm_challenge_continuity(r), ())
        self.assertEqual(an.violations(r.frame, r.duties), {})

    def test_so_temporal_and_inferential_integrity_are_not_enough(self):
        """Stated as a finding: they do not imply non-self-sealing criticism."""
        sealed = c.acs9_pre_existing_self_sealing()
        bespoke = c.acs8_post_hoc_exception()
        self.assertEqual(sv.violations(sealed.docket), {})
        self.assertIn("D1", sv.violations(bespoke.docket))


class TestService(unittest.TestCase):
    """The genuinely new mathematical content, and it is not a closure theorem."""

    def test_starvation_is_invisible_to_everything_qualitative(self):
        """ACS5. Open forever, opportunity forever, nothing served, no defeater.
        Every premise here and in the frozen package is satisfied."""
        r = c.acs5_indefinite_starvation()
        self.assertEqual(sv.violations(r.docket), {})
        self.assertEqual(sv.thm_challenge_continuity(r), ())
        self.assertEqual(an.violations(r.frame, r.duties), {})
        self.assertEqual(
            an.thm_answerability_resolution(r.frame, r.duties), ())

    def test_and_the_service_premise_sees_it(self):
        r = c.acs5_indefinite_starvation()
        bad = sv.s1_service(r)
        self.assertTrue(bad)
        self.assertGreater(bad[0][1], 30.0)          # opportunity accumulated
        self.assertEqual(bad[0][2], 0.0)             # service did not

    def test_the_claim_stays_outstanding_throughout(self):
        """Which is frozen `A1` working correctly, and is exactly the problem:
        an outstanding claim nothing is ever done about."""
        r = c.acs5_indefinite_starvation()
        k = r.docket.all_registered()[0].key
        self.assertIn(k, r.outstanding_keys())

    def test_a_defeated_challenge_is_not_starved(self):
        """S1 counts only open, undefeated challenges."""
        r = c.acs6_resource_priority()
        self.assertEqual(sv.s1_service(r), ())

    def test_service_yields_promotion(self):
        """The consumer lemma, and the whole pipeline in one fixture."""
        r = c.served_to_promotion()
        got = sv.cor_service_yields_promotion(r)
        self.assertEqual(got["c1"][0], 11)
        self.assertGreaterEqual(got["c1"][1], got["c1"][2])


class TestTransferAndMerge(unittest.TestCase):

    def test_duplicates_merge_into_one_successor(self):
        """ACS13. One successor carries both; frozen carry already does it."""
        r = c.acs13_duplicate_challenges()
        self.assertEqual(sv.violations(r.docket), {})
        self.assertEqual(an.violations(r.frame, r.duties), {})
        out = r.outstanding_keys()
        self.assertEqual(len([k for k in out if k[1] in ("c-a", "c-b")]), 0)
        self.assertTrue([k for k in out if k[1] == "c-ab"])

    def test_the_merged_successor_is_the_one_served(self):
        r = c.acs13_duplicate_challenges()
        got = sv.cor_service_yields_promotion(r)
        self.assertIsNotNone(got["c-ab"][0])
        self.assertIsNone(got["c-a"][0])


class TestTheReflectiveCase(unittest.TestCase):

    def test_a_challenge_may_target_a_defeater_rule(self):
        """ACS11. Ordinary machinery; the target is just an identifier."""
        r = c.acs11_challenge_the_defeater_rule()
        self.assertEqual(sv.violations(r.docket), {})
        got = sv.cor_service_yields_promotion(r)
        self.assertIsNotNone(got["c2"][0])
        self.assertIsNone(got["c1"][0])

    def test_no_hierarchy_is_introduced(self):
        tree = ast.parse(inspect.getsource(sv))
        names = {n.id for n in ast.walk(tree) if isinstance(n, ast.Name)}
        names |= {n.attr for n in ast.walk(tree) if isinstance(n, ast.Attribute)}
        for word in ("meta", "level", "hierarchy", "rank"):
            self.assertNotIn(word, names)

    def test_but_admission_of_the_second_challenge_is_not_guaranteed(self):
        """What ACS11 does *not* show. The fixture registers it; nothing here
        says a process must."""
        r = c.acs11_challenge_the_defeater_rule()
        self.assertIn("c2", {x.cid for x in r.docket.all_registered()})
        src = inspect.getsource(sv)
        self.assertNotIn("must_register", src)


class TestTheOuterBoundary(unittest.TestCase):
    """ACS12. What cannot be established from represented history at all."""

    def test_two_worlds_are_indistinguishable(self):
        quiet, also_quiet = c.acs12_indistinguishable_worlds()
        self.assertEqual(quiet.docket.register, also_quiet.docket.register)
        self.assertEqual(sv.violations(quiet.docket),
                         sv.violations(also_quiet.docket))
        self.assertEqual(quiet.incurred_keys(), also_quiet.incurred_keys())
        self.assertEqual(sv.s1_service(quiet), sv.s1_service(also_quiet))

    def test_so_pre_registration_coverage_is_not_provable_here(self):
        """An impossibility observation, not a theorem: no predicate over
        represented history separates a world with no criticism from one whose
        decisive criticism was never registered."""
        quiet, also_quiet = c.acs12_indistinguishable_worlds()
        for probe in (sv.violations, sv.c1_registration_permanence,
                      sv.e1_episode_pinning):
            self.assertEqual(probe(quiet.docket), probe(also_quiet.docket))


class TestTheClosureIsInherited(unittest.TestCase):
    """Third round running. Naming the pattern rather than re-presenting it."""

    def test_continuity_holds_everywhere(self):
        for make in c.ALL:
            r = make()
            with self.subTest(r.name):
                self.assertEqual(sv.thm_challenge_continuity(r), ())

    def test_and_it_is_two_lines_of_A1(self):
        doc = inspect.getdoc(sv.thm_challenge_continuity)
        self.assertIn("inherited", doc)
        self.assertIn("A1", doc)


if __name__ == "__main__":
    unittest.main()
