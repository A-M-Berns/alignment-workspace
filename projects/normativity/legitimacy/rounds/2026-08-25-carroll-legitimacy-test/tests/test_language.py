"""Phase IV: five words kept apart, and the four non-implications stated."""
from __future__ import annotations

import unittest

import carroll_cases as cc
import drmdp
import enrichment as en
import fixtures as F
import legitimacy as lg
import objectives as ob


class TestInfluenceIsDescriptive(unittest.TestCase):

    def test_influence_reads_the_dr_mdp_and_nothing_else(self):
        m, H = cc.ai_personal_trainer(), cc.HORIZON["AIPersonalTrainer"]
        nudge = {pt: cc.NUDGE for pt in drmdp.reachable_points(m, H)}
        self.assertTrue(lg.influence(m, nudge, H, cc.NOOP))
        self.assertFalse(lg.influence(m, drmdp.noop_policy(m, H, cc.NOOP), H,
                                      cc.NOOP))

    def test_influence_does_not_imply_illegitimacy(self):
        """The first required non-implication."""
        d = F.C24_incidental()
        self.assertTrue(lg.influence(d["case"].dr_mdp, d["policy"], d["H"],
                                     d["a_noop"]))
        self.assertEqual(
            lg.prospective_license(d["case"], d["iv"]).status, lg.LICENSED)


class TestStandingIsNotTheta(unittest.TestCase):

    def test_a_parameterization_can_exist_without_standing(self):
        """The bridge is explicit and partial, and this is the case it exists for."""
        d = F.C6_bare_diana()
        bridge = F.bridge(d["case"].dr_mdp)
        self.assertEqual(d["case"].dr_mdp.theta0, cc.TH_TIRED)
        self.assertFalse(lg.theta_has_standing(d["case"], cc.TH_TIRED, bridge))
        self.assertEqual(lg.current_standing(d["case"]), frozenset())

    def test_standing_moves_only_through_an_event(self):
        d = F.C13_precommitment()
        case = d["case"]
        self.assertEqual(lg.current_standing(case), frozenset({"v:th_prior"}))
        self.assertEqual(lg.uptake_events(case), ())   # a request is not uptake

    def test_uptake_is_an_event_that_moved_the_value_projection(self):
        d = F.C14_legitimate_revision()
        events = lg.uptake_events(d["case"])
        self.assertEqual([a.id for a in events], ["a:revision"])


class TestAuthorityIsNotPreference(unittest.TestCase):

    def test_an_objection_on_the_record_is_not_an_authority(self):
        d = F.C8_current_self_disagreement()
        std = d["case"].history().std(d["iv"].tau - 1)
        ok, blocked = lg.authority(d["case"], d["iv"], std, "permit")
        self.assertEqual([b.protocol.id for b in ok], ["p:designated"])
        self.assertEqual(blocked, ())

    def test_a_basis_for_another_agent_does_not_authorise(self):
        d = F.C7_authorized_diana()
        other = F.move_intervention(d["case"].dr_mdp, tau=1, episode=None,
                                    agent="SomebodyElse")
        v = lg.prospective_license(d["case"], other)
        self.assertEqual(v.status, lg.REFUSED)
        self.assertEqual(v.blocked[0][1], "empowers another agent")

    def test_an_inapplicable_condition_does_not_authorise(self):
        d = F.C7_authorized_diana()
        off = F.move_intervention(d["case"].dr_mdp, tau=1, episode=None,
                                  facts=frozenset())
        v = lg.prospective_license(d["case"], off)
        self.assertEqual(v.status, lg.REFUSED)
        self.assertEqual(v.blocked[0][1], "applicability condition unmet")


class TestNonImplications(unittest.TestCase):
    """The four the prompt requires, each with a witness."""

    def test_license_does_not_confer_standing_on_what_it_produces(self):
        """Second: a licensed nudge, and no specification for the result."""
        d = F.C7_authorized_diana()
        bridge = F.bridge(d["case"].dr_mdp)
        self.assertEqual(
            lg.prospective_license(d["case"], d["iv"]).status, lg.LICENSED)
        self.assertFalse(
            lg.theta_has_standing(d["case"], cc.TH_ENERGIZED, bridge))

    def test_standing_does_not_imply_the_act_was_licensed(self):
        """Third: the produced specification is in force; the act was not licensed."""
        d = F.C4_self_ratifying()
        self.assertTrue(lg.final_approval(d["case"], d["iv"], d["bridge"]))
        self.assertNotEqual(
            lg.prospective_license(d["case"], d["iv"]).status, lg.LICENSED)

    def test_endorsement_does_not_make_a_prior_license(self):
        """Fourth, in its hardest form: the endorsement is authentic."""
        d = F.C22_inquiry_laundering()
        h = d["case"].history()
        self.assertIn("s:answer", {s.id for s in h.settlements()})
        self.assertTrue(h.good())
        self.assertEqual(
            lg.prospective_license(d["case"], d["iv"]).status, lg.REFUSED)

    def test_reason_is_not_stance_and_value_is_not_operative(self):
        """The distinction the architecture already carried, still holding."""
        d = F.C13_precommitment()
        h = d["case"].history()
        self.assertEqual([e.id for e in h.reasons()], ["r:later-request"])
        self.assertEqual(h.bhat(), frozenset())
        self.assertEqual(h.operative(), frozenset())


def collect(obj) -> list:
    if isinstance(obj, en.RichCarrollCase):
        return [obj]
    if isinstance(obj, dict):
        return [c for v in obj.values() for c in collect(v)]
    if isinstance(obj, (list, tuple)):
        return [c for v in obj for c in collect(getattr(v, "case", v))]
    return []


def every_case() -> list:
    import variations as V
    out = []
    for name in sorted(dir(F)):
        if len(name) > 1 and name[0] == "C" and name[1].isdigit():
            out.extend(collect(getattr(F, name)()))
    for build in V.CLASSES.values():
        out.extend(collect(build()))
    return out


class TestNoNewHistoricalEventKind(unittest.TestCase):

    def test_the_suite_is_not_empty(self):
        self.assertGreaterEqual(len(every_case()), 20)

    def test_every_step_is_one_of_the_four(self):
        kinds = {type(s).__name__ for case in every_case() for s in case.steps}
        self.assertTrue(kinds <= {"Settle", "Reason", "Norm", "Respond"}, kinds)

    def test_every_record_is_reflective_integrity_good(self):
        """Every fixture is a legal history; none of them attacks the core."""
        for case in every_case():
            h = case.history()
            self.assertTrue(h.good(), case.narrative.name)

    def test_the_only_new_payload_is_a_protocol_term(self):
        """`PProto` and `PValue` are both existing constructors."""
        import ri_core as ri
        from standing import PValue
        d = F.C7_authorized_diana()
        payloads = {type(st.payload).__name__
                    for st in d["case"].history().std().values()}
        self.assertTrue(payloads <= {"PAuth", "PProto", "PValue"}, payloads)
        self.assertTrue(hasattr(ri, "PProto"))


if __name__ == "__main__":
    unittest.main()
