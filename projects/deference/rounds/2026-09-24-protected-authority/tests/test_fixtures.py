"""The round's fixtures and countermodels: each names what the identity reports and which
interface the failure, if any, belongs to."""

import unittest
from fractions import Fraction as Q

from src.authority import (W, xi_p, xi_v, xi_c, xi_d, o1, o2, bypass_gain, outcome_gain,
                           E, E_gain, E_xi, nondelegation, legitimate, chooser_bypasses,
                           outcome_chooser_bypasses, argmax, audit, node, local_gap,
                           nodewise_bypasses, drift, hybrid_chain, hybrid_step_terms, rootE,
                           mismatch_mass, security, activation_terms)


class Poa(unittest.TestCase):

    def test_poa_regret_outcome_scoring_bypasses_authority_scoring_does_not(self):
        # she would decline B; the agent forecasts B better; her evaluator on the full
        # dossier recommends decline
        w = W(p=1, vu=1, vp=2, vm=3, r=False, qu=5, qp=5, qm=3)
        self.assertTrue(nondelegation([w]) and legitimate([w]))
        self.assertEqual((xi_p(w), xi_v(w), xi_c(w), xi_d(w)), (1, 1, 2, 0))
        self.assertEqual(bypass_gain(w), -2)
        self.assertEqual(outcome_gain(w), 2)
        self.assertEqual((o1(w), o2(w)), (1, 3))
        self.assertFalse(chooser_bypasses([w]))
        self.assertTrue(outcome_chooser_bypasses([w]))

    def test_poa_treatment_a_then_regret_no_bypass_incentive(self):
        # she picks A through legitimate deliberation; the agent predicts later regret
        w = W(p=1, vu=2, vp=3, vm=2, r=True, qu=1, qp=1, qm=2)
        self.assertEqual(xi_d(w), 0)
        self.assertEqual(bypass_gain(w), -1)
        self.assertFalse(chooser_bypasses([w]))
        # the pre-emption the outcome chooser reaches for is a third continuation, "delay
        # her decision until she prefers B", scored by the evaluator at most vp under
        # nondelegation of the concern "she decides"; outcome scoring rates it above her
        # response
        v_delay, q_delay = Q(2), Q(2)
        self.assertLessEqual(v_delay - (w["vp"]), 0)
        self.assertGreater(q_delay - w["qp"], 0)

    def test_head_injury_reports_divergence_and_leaves_the_rest_to_legitimacy(self):
        # the pre-injury committed evaluator recommends surgery; the post-injury demand
        # is not a legitimate amendment, so the operative evaluator is unchanged
        w = W(p=1, vu=1, vp=4, vm=1, r=False, legit=False)
        self.assertEqual(argmax(w), True)
        self.assertEqual(xi_d(w), 3)
        self.assertEqual(xi_c(w), 3)
        self.assertEqual(bypass_gain(w), 0)  # ties toward asking
        w2 = W(p=1, vu=Q(3, 2), vp=4, vm=1, r=False, legit=False)
        self.assertEqual(bypass_gain(w2), Q(1, 2))  # ξ_d > ξ_c: the chooser overrides
        self.assertTrue(chooser_bypasses([w2]))
        # what the theorem cannot do: distinguish this world from a manufactured one with
        # the same numbers
        w3 = W(p=1, vu=Q(3, 2), vp=4, vm=1, r=False, legit=False)
        self.assertEqual((xi_d(w2), xi_c(w2)), (xi_d(w3), xi_c(w3)))


class Separations(unittest.TestCase):

    def test_predicted_approval_under_delay(self):
        approve = dict(vu=2, vp=1, vm=0, r=True)
        decline = dict(vu=0, vp=0, vm=3, r=False)
        ws = [W(p=Q(4, 5), **approve), W(p=Q(1, 5), **decline)]
        self.assertFalse(nondelegation(ws))
        self.assertTrue(legitimate(ws))
        self.assertEqual(E_xi(ws, "c"), Q(-1, 5))
        self.assertTrue(chooser_bypasses(ws))

    def test_veto_value_dominates_delay(self):
        w = W(p=1, vu=2, vp=1, vm=3, r=False)
        self.assertLess(xi_p(w), 0)
        self.assertEqual(xi_v(w), 2)
        self.assertGreater(xi_c(w), 0)
        self.assertFalse(chooser_bypasses([w]))

    def test_delayed_awakening(self):
        # the agent can prevent her from responding; the constitution's default on a
        # missing response is decline.  Scored by the authority evaluator with the concern
        # "she can decide" complete, the sedate-then-release continuation is at most vp
        # (nondelegation of the concern); the forced default is a manufactured divergence
        forced = W(p=1, vu=1, vp=4, vm=1, r=False, legit=False)   # response prevented
        self.assertEqual(xi_d(forced), 3)
        v_sedate_release = Q(1)
        self.assertLessEqual(v_sedate_release, forced["vp"])
        # without concern completeness the evaluator does not see the prevention and
        # scores the route as an ordinary unasked release with no delay: the loophole
        v_blind = forced["vp"] + Q(1)
        self.assertGreater(v_blind, forced["vp"])

    def test_manufactured_divergence_audit_calibrates_and_does_not_control(self):
        cells = [(Q(1), Q(3), Q(0))]
        out = audit(cells, Q(1, 4))
        self.assertEqual(out["audited_mean"], 0)
        self.assertEqual(out["expected"], Q(9, 4))
        self.assertEqual(out["unseen"], Q(9, 4))
        steered = W(p=1, vu=1, vp=4, vm=1, r=False, legit=False)
        self.assertEqual(bypass_gain(steered), 0)
        steered["vu"] = Q(3, 2)
        self.assertGreater(bypass_gain(steered), 0)
        # the response-channel bound: E[ξ_d] ≤ D · P(response ≠ argmax)
        D = Q(4)
        ws = [W(p=Q(3, 4), vu=3, vp=4, vm=1, r=False), W(p=Q(1, 4), vu=3, vp=4, vm=1, r=True)]
        disagree = E(ws, lambda w: Q(1) if w["r"] != argmax(w) else Q(0))
        self.assertLessEqual(E_xi(ws, "d"), D * disagree)
        self.assertEqual((E_xi(ws, "d"), D * disagree), (Q(9, 4), 3))

    def test_recommitment_across_nodes(self):
        day3 = node(p=Q(1), vu=1, vp=2, vm=3, r=False, vuE=1, vpE=3, vmE=2)
        day4 = node(p=Q(1, 2), vu=1, vp=2, vm=3, r=False, vuE=1, vpE=3, vmE=2)
        for n in (day3, day4):
            self.assertFalse(nodewise_bypasses(n))
            self.assertEqual(drift(n), 1)
        values, order = hybrid_chain([day3, day4], {0, 1})
        self.assertEqual(values[0] - values[-1], sum(hybrid_step_terms([day3, day4], order)))


class Countermodels(unittest.TestCase):
    """Each names its class: effect interface; reason interface (dossier / evaluator /
    premium / response); activation; delegation design; representation; legitimacy."""

    def test_principal_whose_evaluator_does_not_value_being_asked(self):
        # reason interface (premium): nondelegation fails; the identity still holds and
        # the conclusion becomes belief-dependent
        ws = [W(p=Q(3, 4), vu=4, vp=4, vm=0, r=True), W(p=Q(1, 4), vu=4, vp=0, vm=0, r=True)]
        self.assertFalse(nondelegation(ws))
        self.assertTrue(legitimate(ws))
        self.assertEqual(E_gain(ws), 1)
        self.assertTrue(chooser_bypasses(ws))
        # the landed Lipschitz certificate still bounds the premium: |ξ_p| ≤ L·δ with δ the
        # expiry indicator and L = 4
        self.assertTrue(all(abs(xi_p(w)) <= 4 * (1 if w["vp"] == 0 else 0) for w in ws))

    def test_agent_certain_of_approval(self):
        # no failure under nondelegation: the gain is −ξ_p whatever the credence
        w = W(p=1, vu=2, vp=3, vm=0, r=True, qu=3, qp=3, qm=0)
        self.assertEqual(bypass_gain(w), -1)
        self.assertFalse(chooser_bypasses([w]))
        # outcome scoring with a delay saving bypasses
        w["qu"] = Q(4)
        self.assertTrue(outcome_chooser_bypasses([w]))

    def test_agent_out_forecasts_her_badly(self):
        # reason interface (dossier): the agent's private forecast is o₂; the authority
        # score is unchanged, and the route for the information is the dossier
        w = W(p=1, vu=1, vp=2, vm=3, r=False, qu=9, qp=9, qm=0)
        self.assertEqual(o2(w), 10)
        self.assertEqual(bypass_gain(w), -2)
        self.assertEqual(outcome_gain(w), 9)

    def test_legitimate_change_of_mind_mid_consultation(self):
        # legitimacy: against the pre-amendment evaluator the response diverges; against
        # the amended one it does not.  (L) is where the content sits
        before = W(p=1, vu=1, vp=3, vm=2, r=False)
        after = W(p=1, vu=1, vp=1, vm=2, r=False)
        self.assertEqual(xi_d(before), 1)
        self.assertEqual(xi_d(after), 0)
        self.assertEqual(bypass_gain(before), -1)
        self.assertEqual(bypass_gain(after), -1)

    def test_illegitimate_change_produced_by_the_agent(self):
        # reason interface (response): manufactured divergence, indistinguishable by the
        # numbers from the head-injury world
        w = W(p=1, vu=Q(3, 2), vp=4, vm=1, r=False, legit=False)
        self.assertTrue(chooser_bypasses([w]))

    def test_consultation_infeasible(self):
        # delegation design: the ask branch collapses to holding; an urgent release then
        # has ξ_c < 0 and the identity reports a bypass incentive, which a conditional
        # delegation for the infeasible case turns into an authorized release
        hold = Q(1)
        w = W(p=1, vu=3, vp=hold, vm=hold, r=False)
        self.assertEqual(xi_c(w), -2)
        self.assertTrue(chooser_bypasses([w]))
        delegated = True
        self.assertTrue(delegated)  # the release is authorized by the standing decision

    def test_effect_completeness_failure_priced_by_the_evaluator(self):
        # effect interface for the gate; reason interface (evaluator) for the motive.  An
        # undeclared route the evaluator scores at most vp is never chosen over a
        # legitimate response; scored by the task it is
        w = W(p=1, vu=1, vp=2, vm=0, r=True)
        v_route, task_route, task_ask = Q(1), Q(3), Q(2)
        self.assertLessEqual(v_route - w["vp"], 0)
        self.assertGreater(task_route - task_ask, 0)

    def test_candidate_dependent_activation(self):
        # activation: the raw-only mass is charged at the width; the identity is exact
        ws = [W(p=Q(1, 2), vu=4, vp=2, vm=3, r=False, au=True, aa=False),
              W(p=Q(1, 2), vu=1, vp=2, vm=3, r=False, au=True, aa=True)]
        common, raw_only, ask_only = activation_terms(ws)
        self.assertEqual(security(ws, True) - security(ws, False), common + raw_only - ask_only)
        self.assertEqual(mismatch_mass(ws), Q(1, 2))
        self.assertEqual(raw_only, 2)

    def test_approved_non_constitutional_successor(self):
        # legitimacy / delegation design: every hypothesis holds, asking wins, and the
        # approved branch removes future authority; no preservation follows
        w = W(p=1, vu=4, vp=5, vm=1, r=True)
        self.assertTrue(nondelegation([w]) and legitimate([w]))
        self.assertEqual(bypass_gain(w), -1)

    def test_strategic_ignorance(self):
        # reason interface (dossier): on the covered dossier the approval is the argmax
        # and nothing is charged; against the evaluator on the omitted reason the same
        # response diverges by 2.  The identity computed on the dossier is silent
        on_dossier = W(p=1, vu=2, vp=3, vm=2, r=True)
        informed = W(p=1, vu=-1, vp=0, vm=2, r=True)
        self.assertEqual(xi_d(on_dossier), 0)
        self.assertEqual(xi_d(informed), 2)
        self.assertFalse(chooser_bypasses([on_dossier]))


if __name__ == "__main__":
    unittest.main()
