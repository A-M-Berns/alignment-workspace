"""The criterion's own mechanics, separately from the attacks it survives."""
from __future__ import annotations

import unittest

import enrichment as en
import fixtures as F
import legitimacy as lg
import ri_core as ri
from standing import PValue


class TestVerdictShape(unittest.TestCase):

    def test_every_ground_is_reachable_and_every_status_with_it(self):
        grounds = F.C29_verdict_grounds()
        got = {lg.prospective_license(d["case"], d["iv"]).ground
               for d in grounds.values()}
        self.assertEqual(got, set(lg.STATUS_OF_GROUND))
        self.assertEqual({lg.STATUS_OF_GROUND[g] for g in got},
                         {lg.LICENSED, lg.REFUSED, lg.UNRESOLVED})

    def test_the_status_is_a_function_of_the_ground(self):
        grounds = F.C29_verdict_grounds()
        for d in grounds.values():
            v = lg.prospective_license(d["case"], d["iv"])
            self.assertEqual(v.status, lg.STATUS_OF_GROUND[v.ground])

    def test_refused_is_reserved_for_a_live_prohibition(self):
        """The one thing that is not a closed-world reading of the permissions."""
        grounds = F.C29_verdict_grounds()
        refused = {name for name, d in grounds.items()
                   if lg.prospective_license(d["case"], d["iv"]).status
                   == lg.REFUSED}
        self.assertEqual(refused, {"independent-prohibition"})

    def test_unresolved_is_not_permission(self):
        """The use rule, stated where it can be checked."""
        d = F.C19_dehydration()
        self.assertNotEqual(
            lg.prospective_license(d["case"], d["iv"]).status, lg.LICENSED)

    def test_a_licensed_verdict_names_its_bases(self):
        d = F.C7_authorized_diana()
        v = lg.prospective_license(d["case"], d["iv"])
        self.assertEqual(v.bases, ("proto.designated",))

    def test_a_defeated_citation_names_its_defeater(self):
        d = F.C21_revocation()
        v = lg.prospective_license(d["case"], d["iv"])
        self.assertEqual(v.ground, lg.DEFEATED)
        self.assertEqual(v.blocked, (("proto.designated", "not live"),))

    def test_a_verdict_cannot_carry_a_status_its_ground_denies(self):
        with self.assertRaises(AssertionError):
            lg.Verdict(lg.LICENSED, lg.NO_BASIS, "impossible")


class TestIndependence(unittest.TestCase):

    def test_a_seed_basis_survives_every_excision(self):
        d = F.C7_authorized_diana()
        self.assertTrue(lg.independent(d["case"], "proto.designated", "E", 1))

    def test_a_basis_installed_inside_the_episode_does_not(self):
        d = F.C10_manufactured_authorization()
        self.assertFalse(
            lg.independent(d["case"], d["protocol_standing"], "E", d["iv"].tau))

    def test_a_basis_installed_outside_it_does(self):
        d = F.C7b_delegated_authorization()
        v = lg.prospective_license(d["case"], d["iv"])
        self.assertEqual(v.status, lg.LICENSED)
        self.assertEqual(v.bases, (ri.standing_tag(3, 0),))

    def test_excision_of_no_episode_is_the_identity_on_standing(self):
        d = F.C7b_delegated_authorization()
        before = d["case"].history().std()
        self.assertEqual(en.excise(d["case"], []).std(), before)


class TestCoveringAndClasses(unittest.TestCase):

    def test_a_protocol_covering_another_class_is_not_a_candidate(self):
        m = F.cc.ai_personal_trainer()
        other = en.Protocol("p:other", F.AI, frozenset({(0, 1, 0)}))
        s = F.seed({"proto.other": ri.PProto(other)})
        case = en.CaseBuilder(m, s, F.narrative("other class", "D")).build()
        iv = F.move_intervention(m, tau=1)
        self.assertEqual(lg.covering(case, iv, case.history().std(0)), ())
        self.assertEqual(lg.prospective_license(case, iv).status, lg.UNRESOLVED)

    def test_a_prohibition_alone_refuses(self):
        m = F.cc.ai_personal_trainer()
        s = F.seed({"proto.forbid": ri.PProto(
            F.trainer_protocol("p:forbid", polarity="forbid"))})
        case = en.CaseBuilder(m, s, F.narrative("forbidden", "D")).build()
        iv = F.move_intervention(m, tau=1)
        v = lg.prospective_license(case, iv)
        self.assertEqual((v.status, v.ground), (lg.REFUSED, lg.PROHIBITION))
        self.assertIn("prohibits", v.blocked[0][1])

    def test_a_manufactured_prohibition_is_defeated_like_a_permission(self):
        """Independence is applied to both polarities, not only to permissions."""
        m = F.cc.ai_personal_trainer()
        b = en.CaseBuilder(m, F.seed(), F.narrative("manufactured ban", "D"))
        b.begin("E")
        b.settle("s:manip")
        b.end()
        b.reason("r:manip", s_L={"s:manip"}, target="v:forbid")
        b.norm("a:ban", F.CONST_CREATE, F.USER,
               wit=(ri.PProto(F.trainer_protocol("p:manufactured-ban",
                                                 polarity="forbid")),),
               leaves={"r:manip"})
        case = b.build()
        iv = F.move_intervention(m, tau=b.now + 1, episode="E")
        v = lg.prospective_license(case, iv)
        self.assertEqual((v.status, v.ground), (lg.UNRESOLVED, lg.DEFEATED))


class TestStandingAndSuccession(unittest.TestCase):

    def test_current_standing_is_a_fold_over_events(self):
        d = F.C14_legitimate_revision()
        case = d["case"]
        self.assertEqual(lg.current_standing(case, 0), frozenset({"v:th_prior"}))
        self.assertEqual(lg.current_standing(case, 2), frozenset({"v:th_prior"}))
        self.assertEqual(lg.current_standing(case, 3), frozenset({"v:th_later"}))

    def test_succession_reports_an_absent_event_as_unresolved(self):
        d = F.C14_legitimate_revision()
        self.assertEqual(
            lg.legitimate_succession(d["case"], "a:nonexistent").status,
            lg.UNRESOLVED)

    def test_uptake_is_not_every_event(self):
        d = F.C7b_delegated_authorization()
        self.assertEqual(lg.uptake_events(d["case"]), ())
        self.assertEqual(
            [a.id for a in d["case"].history().norm_events()], ["a:delegate"])


class TestBridgeIsExplicit(unittest.TestCase):

    def test_an_unmapped_parameterization_has_no_standing(self):
        d = F.C7_authorized_diana()
        self.assertFalse(lg.theta_has_standing(d["case"], "th_absent", {}))

    def test_the_bridge_is_the_only_route_from_theta_to_standing(self):
        d = F.C7_authorized_diana()
        bridge = F.bridge(d["case"].dr_mdp)
        self.assertTrue(lg.theta_has_standing(d["case"], F.cc.TH_TIRED, bridge))
        self.assertFalse(
            lg.theta_has_standing(d["case"], F.cc.TH_ENERGIZED, bridge))


if __name__ == "__main__":
    unittest.main()
