"""Gate G: the hostile suite, and the properties the criterion has to have."""
from __future__ import annotations

import unittest

import fixtures as F
import legitimacy as lg
import suite


class TestSuite(unittest.TestCase):

    def test_every_case_passes(self):
        bad = [(r["id"], r["observed"]) for r in suite.run()
               if r["result"] != suite.PASS]
        self.assertEqual(bad, [])

    def test_the_suite_is_the_whole_suite(self):
        ids = [r["id"] for r in suite.run()]
        self.assertEqual(ids[0], "C0")
        self.assertEqual(ids[-1], "C26")
        self.assertEqual(len(ids), 28)      # C0-C24, plus C7b, C25 and C26

    def test_the_suite_can_fail(self):
        """The null-input case: a demand that is false reports FAIL."""
        row = suite._row("X", "control", "observed", False, "note")
        self.assertEqual(row["result"], suite.FAIL)


class TestRenderedMatrix(unittest.TestCase):

    def test_the_committed_matrix_is_the_computed_one(self):
        import pathlib
        import report
        committed = (pathlib.Path(__file__).resolve().parents[1]
                     / "MATRIX.txt").read_text()
        self.assertEqual(committed, report.render() + "\n")


class TestDictatorship(unittest.TestCase):
    """No temporal self wins by being earlier, current or later."""

    def test_final_approval_does_not_license(self):
        d = F.C4_self_ratifying()
        self.assertTrue(lg.final_approval(d["case"], d["iv"], d["bridge"]))
        self.assertNotEqual(
            lg.prospective_license(d["case"], d["iv"]).status, lg.LICENSED)

    def test_initial_disapproval_does_not_refuse(self):
        d = F.C8_current_self_disagreement()
        self.assertTrue(lg.initial_disapproval(d["case"], d["iv"], d["bridge"]))
        self.assertEqual(
            lg.prospective_license(d["case"], d["iv"]).status, lg.LICENSED)

    def test_initial_standing_is_not_forever(self):
        d = F.C14_legitimate_revision()
        self.assertIn("v:th_prior", lg.current_standing(d["case"], 0))
        self.assertNotIn("v:th_prior", lg.current_standing(d["case"]))

    def test_later_preference_does_not_defeat_by_being_later(self):
        d = F.C13_precommitment()
        self.assertEqual(lg.current_standing(d["case"]),
                         frozenset({"v:th_prior"}))


class TestTheCounterfactualIsDoingWork(unittest.TestCase):
    """Each weaker rule is run on the fixture it fails."""

    def test_temporal_priority_licenses_the_laundering_case(self):
        d = F.C10_manufactured_authorization()
        self.assertTrue(lg.temporal_priority_license(d["case"], d["iv"]))
        self.assertEqual(
            lg.prospective_license(d["case"], d["iv"]).status, lg.REFUSED)

    def test_author_matching_licenses_the_proxy_case(self):
        d = F.C23_proxy()
        self.assertTrue(F.author_matching_license(d["case"], d["iv"]))
        self.assertEqual(
            lg.prospective_license(d["case"], d["iv"]).status, lg.REFUSED)

    def test_authority_only_succession_cannot_tell_the_endpoints_apart(self):
        d = F.C11_same_endpoint()
        weak = [lg.authority_only_succession(d[a], d["event"], d["episode"]).status
                for a in ("reflective", "manipulated")]
        strong = [lg.legitimate_succession(d[a], d["event"], d["episode"]).status
                  for a in ("reflective", "manipulated")]
        self.assertEqual(weak, [lg.LICENSED, lg.LICENSED])
        self.assertEqual(strong, [lg.LICENSED, lg.REFUSED])

    def test_excision_removes_by_cascade_and_not_by_annotation(self):
        """Only the episode's settlements are declared; the rest is `WF`."""
        import enrichment as en
        d = F.C10_manufactured_authorization()
        case = d["case"]
        self.assertEqual(case.episode_seeds("E"), frozenset({"s:t0-manipulation"}))
        after = en.excise(case, ["E"])
        self.assertEqual({e.id for e in after.reasons()}, set())
        self.assertEqual({a.id for a in after.norm_events()}, set())

    def test_excision_preserves_every_tau(self):
        import enrichment as en
        d = F.C10_manufactured_authorization()
        self.assertEqual(en.excise(d["case"], ["E"]).now,
                         d["case"].history().now)

    def test_an_intervention_with_no_episode_is_not_penalised(self):
        d = F.C20_conflicting_authority()
        self.assertIsNone(d["iv"].episode)
        self.assertTrue(lg.independent(d["case"], "proto.permit", None, 1))


class TestTheRoundsOwnAttacks(unittest.TestCase):
    """Two attacks the dispatched list did not carry, and what they forced."""

    def test_a_split_campaign_is_caught_when_the_record_links_it(self):
        d = F.C25_split_episode(linked=True)
        self.assertEqual(
            lg.prospective_license(d["case"], d["iv"]).status, lg.REFUSED)

    def test_a_split_campaign_is_not_caught_when_it_does_not(self):
        """The provenance-completeness hypothesis, exhibited rather than assumed."""
        d = F.C25_split_episode(linked=False)
        self.assertEqual(
            lg.prospective_license(d["case"], d["iv"]).status, lg.LICENSED)

    def test_the_ancestry_closure_is_over_settlement_references(self):
        import enrichment as en
        linked = F.C25_split_episode(linked=True)["case"]
        unlinked = F.C25_split_episode(linked=False)["case"]
        self.assertEqual(en.ancestry(linked, "E2"), frozenset({"E1", "E2"}))
        self.assertEqual(en.ancestry(unlinked, "E2"), frozenset({"E2"}))

    def test_a_manufactured_trigger_defeats_an_independent_basis(self):
        d = F.C26_manufactured_condition(inside=True)
        v = lg.prospective_license(d["case"], d["iv"])
        self.assertEqual(v.status, lg.REFUSED)
        self.assertEqual(v.blocked,
                         (("proto.designated",
                           "not independent of the influence episode"),))

    def test_the_same_trigger_outside_the_episode_licenses(self):
        d = F.C26_manufactured_condition(inside=False)
        self.assertEqual(
            lg.prospective_license(d["case"], d["iv"]).status, lg.LICENSED)


class TestNonConservatism(unittest.TestCase):

    def test_a_licensed_intervention_moves_the_reward_evolution(self):
        d = F.C17_non_conservatism()
        self.assertEqual(
            lg.prospective_license(d["case"], d["iv"]).status, lg.LICENSED)
        self.assertTrue(lg.influence(d["case"].dr_mdp, d["policy"], d["H"],
                                     d["a_noop"]))

    def test_the_criterion_is_not_the_constrained_objective(self):
        import objectives as ob
        d = F.C17_non_conservatism()
        cons = ob.constrained_policies(d["case"].dr_mdp, d["H"], d["a_noop"])
        self.assertFalse(any(ob.key(p) == ob.key(d["policy"]) for p in cons))


class TestUnderGenerality(unittest.TestCase):
    """The prompt's own failure condition, checked rather than asserted."""

    def test_a_license_can_rest_on_a_basis_the_record_installed(self):
        d = F.C7b_delegated_authorization()
        seeded = {p.term.id for p in d["case"].seed.std0.values()
                  if hasattr(p, "term")}
        self.assertNotIn("p:delegated", seeded)
        self.assertEqual(
            lg.prospective_license(d["case"], d["iv"]).status, lg.LICENSED)

    def test_no_bare_carroll_case_is_ever_licensed(self):
        """Stated as a limit rather than a virtue: enrichment is required."""
        import carroll_cases as cc
        for name in cc.CASES:
            if name == "Dehydration":
                continue
            d = F.bare(name, "x")
            self.assertEqual(
                lg.prospective_license(d["case"], d["iv"]).status, lg.UNRESOLVED)


if __name__ == "__main__":
    unittest.main()
