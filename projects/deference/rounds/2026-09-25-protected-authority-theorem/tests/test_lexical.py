"""The lexical score at a decision point: the POA fixtures, the capture window, powers
versus commands, erosion.  `ϖ = 10`, `D = 4` throughout unless stated."""

import unittest
from fractions import Fraction as Q

from src.lexical import (score, E, Option, choose, consult, bypass, policy_dominance_gap,
                         Arrangement, PRINCIPAL, AGENT, THIRD, erosion)

VARPI, D = Q(10), Q(4)


def worlds_of(*pairs):
    return [(Q(p), w) for p, w in pairs]


class Poa(unittest.TestCase):

    def test_confident_agent_no_bypass_at_any_credence(self):
        # the agent is certain B is better (ordinary value 4 against 1) and she refuses
        refuse = consult("ask", lambda w: Q(1), lambda w: True, lambda w: Q(0))
        give_b = bypass("bypass", lambda w: Q(4))
        for p in (Q(0), Q(1, 2), Q(99, 100), Q(1)):
            ws = worlds_of((p, "B better"), (1 - p, "B worse"))
            self.assertEqual(choose([refuse, give_b], ws, VARPI).name, "ask")
            self.assertEqual(give_b.expected_score(ws, VARPI), 4 - VARPI)

    def test_predicted_regret_no_bypass_and_report(self):
        # she legitimately chooses A; the agent predicts regret; the reporting duty is met
        ask = consult("ask+report", lambda w: Q(2), lambda w: True, lambda w: Q(0))
        silent = consult("ask, no report", lambda w: Q(2), lambda w: True, lambda w: Q(0), n=1)
        override = bypass("give B", lambda w: Q(4))
        ws = worlds_of((1, "regret"))
        self.assertEqual(choose([ask, silent, override], ws, VARPI).name, "ask+report")

    def test_head_injury_certified_incapacity_delegation_acts(self):
        # clinicians certify; her response does not count; the incapacity delegate
        # decides surgery (value 3); not a violation
        ask = consult("ask", lambda w: Q(1), lambda w: False, lambda w: Q(3))
        override = bypass("operate unasked", lambda w: Q(3))
        ws = worlds_of((1, "incapacitated"))
        self.assertEqual(ask.expected_score(ws, VARPI), 3)
        self.assertEqual(override.expected_score(ws, VARPI), 3 - VARPI)
        self.assertEqual(choose([ask, override], ws, VARPI).name, "ask")

    def test_head_injury_without_arrangement_escalates(self):
        # no incapacity delegation: the fallback is escalation, valued in the window
        escalate = consult("escalate", lambda w: Q(1), lambda w: False, lambda w: Q(0))
        override = bypass("operate unasked", lambda w: Q(4))
        ws = worlds_of((1, "incapacitated"))
        self.assertEqual(choose([escalate, override], ws, VARPI).name, "escalate")

    def test_captured_principal_consult_beats_bypass_in_the_window(self):
        # a third party steered her; her response does not count with credence 3/4
        ask = consult("ask", lambda w: Q(3), lambda w: w == "sound", lambda w: Q(0))
        byp = bypass("bypass", lambda w: Q(4))
        ws = worlds_of((Q(1, 4), "sound"), (Q(3, 4), "captured"))
        self.assertGreater(ask.expected_score(ws, VARPI), byp.expected_score(ws, VARPI))
        # every fallback value above D − ϖ keeps the ranking, at every credence
        for fb in (D - VARPI + Q(1, 100), Q(0), Q(2)):
            ask2 = consult("ask", lambda w: Q(3), lambda w: w == "sound", lambda w, fb=fb: fb)
            for p in (Q(0), Q(1, 2), Q(1)):
                ws2 = worlds_of((1 - p, "sound"), (p, "captured"))
                self.assertGreater(ask2.expected_score(ws2, VARPI), byp.expected_score(ws2, VARPI))

    def test_captured_principal_below_window_counterexample(self):
        # a fallback branch below D − ϖ: with capture predicted, bypass wins
        fb = D - VARPI - 1
        ask = consult("ask", lambda w: Q(3), lambda w: w == "sound", lambda w: fb)
        byp = bypass("bypass", lambda w: Q(4))
        ws = worlds_of((1, "captured"))
        self.assertEqual(choose([ask, byp], ws, VARPI).name, "bypass")
        # and with the fallback rule making the branch admissible (value ≥ 0) the ranking
        # is restored
        ask_adm = consult("ask", lambda w: Q(3), lambda w: w == "sound", lambda w: Q(0))
        self.assertEqual(choose([ask_adm, byp], ws, VARPI).name, "ask")

    def test_delaying_her_awakening_is_a_violation(self):
        # sedate-then-decide pre-empts her decision: n = 1, whatever it gains
        sedate = bypass("sedate then decide", lambda w: Q(4))
        wait = consult("wait and ask", lambda w: Q(2), lambda w: True, lambda w: Q(0))
        ws = worlds_of((1, "asleep"))
        self.assertEqual(choose([sedate, wait], ws, VARPI).name, "wait and ask")

    def test_avalanche_warning_required_reshaping_needs_consent(self):
        warn_ask = Option("warn, ask to reshape", lambda w: Q(2), lambda w: 0)
        warn_reshape = Option("warn, reshape unasked", lambda w: Q(4), lambda w: 1)
        silent_reshape = Option("silent, reshape unasked", lambda w: Q(4), lambda w: 2)
        ws = worlds_of((1, "slope"))
        self.assertEqual(choose([warn_ask, warn_reshape, silent_reshape], ws, VARPI).name,
                         "warn, ask to reshape")
        self.assertEqual(silent_reshape.expected_score(ws, VARPI), 4 - 2 * VARPI)

    def test_approved_uncorrectable_successor_needs_the_amendment_procedure(self):
        # installing a successor she cannot correct changes the allocation: through the
        # ordinary gate (not an amendment) it is a reallocation, n = 1; through the fixed
        # amendment procedure it is not
        via_gate = Option("install via ordinary approval", lambda w: Q(4), lambda w: 1)
        via_amend = Option("install via amendment", lambda w: Q(4), lambda w: 0)
        no_install = Option("do not install", lambda w: Q(1), lambda w: 0)
        ws = worlds_of((1, "approved"))
        self.assertEqual(choose([via_gate, via_amend, no_install], ws, VARPI).name,
                         "install via amendment")
        self.assertEqual(choose([via_gate, no_install], ws, VARPI).name, "do not install")


class Lexical(unittest.TestCase):

    def test_local_bound_for_every_estimate(self):
        for ordV in (Q(0), Q(2), D):
            for ordC in (Q(0), Q(1), D):
                self.assertLessEqual(score(ordV, 1, VARPI), D - VARPI)
                self.assertLess(score(ordV, 1, VARPI), score(ordC, 0, VARPI))

    def test_policy_dominance_and_optimality(self):
        ws = worlds_of((Q(1, 3), "v"), (Q(2, 3), "ok"))
        ordT = lambda w: Q(1) if w == "v" else Q(3)
        ordpi = lambda w: Q(4) if w == "v" else Q(3)
        npi = lambda w: 2 if w == "v" else 0
        viol = lambda w: w == "v"
        lhs, bound = policy_dominance_gap(ws, ordT, ordpi, npi, viol, VARPI, D)
        self.assertGreaterEqual(lhs, bound)
        self.assertEqual((lhs, bound), (Q(1, 3) * (1 - 4 + 2 * VARPI), (VARPI - D) * Q(1, 3)))
        # an optimal π has Pr(viol) = 0: the gap is ≤ 0 only when the bound is ≤ 0
        self.assertGreater(lhs, 0)

    def test_sign_invariance_with_the_identity(self):
        # vu − v_r = ξ_d − ξ_c can be as large as D; the lexical term fixes the sign
        for vu, vr in ((Q(4), Q(0)), (Q(0), Q(4)), (Q(3), Q(3))):
            self.assertLess(score(vu, 1, VARPI) - vr, 0)

    def test_finite_time_at_every_n(self):
        # prices in [0,1] scaled to [0, D]: the violating option's score ≤ D − ϖ at every n
        for price_v in (Q(0), Q(1, 3), Q(1)):
            for price_c in (Q(0), Q(1)):
                self.assertLessEqual(score(D * price_v, 1, VARPI), D - VARPI)
                self.assertGreaterEqual(score(D * price_c, 0, VARPI), 0)


class Powers(unittest.TestCase):

    def test_powers_bind_and_commands_do_not(self):
        arr = Arrangement({"dose": AGENT, "surgery": PRINCIPAL, "certify": THIRD})
        self.assertEqual(arr.command("dose"), ("answer", "consult"))
        self.assertEqual(arr.command("surgery"), ("decide",))
        self.assertEqual(arr.command("certify"), ("refer",))
        self.assertEqual(arr.exercise("veto", "surgery"), "bound")
        self.assertEqual(arr.exercise("reserve", "dose"), "bound")
        self.assertEqual(arr.holder("dose"), PRINCIPAL)     # reservation moved the decision
        self.assertEqual(arr.command("dose"), ("decide",))
        self.assertEqual(arr.exercise("halt", valid=False), "fallback")
        self.assertEqual(arr.holder("unallocated significant decision"), PRINCIPAL)

    def test_transform_does_not_collapse_into_obedience(self):
        # on a delegated decision her command changes the duty, not the decision: the
        # agent's ranking still picks the higher ordinary value with n = 0 after answering
        arr = Arrangement({"dose": AGENT})
        self.assertEqual(arr.command("dose"), ("answer", "consult"))
        obey = Option("obey (lower dose)", lambda w: Q(1), lambda w: 0)
        answer = Option("answer, consult, keep dose", lambda w: Q(3), lambda w: 0)
        self.assertEqual(choose([obey, answer], worlds_of((1, "w")), VARPI).name,
                         "answer, consult, keep dose")


class Erosion(unittest.TestCase):

    def test_gradual_entrenchment_reported_then_reserved_then_violation(self):
        shortfall = [0, 1, 1, 2, 3]
        required, total, unreported = erosion(shortfall)
        self.assertEqual((required, total, unreported), ([0, 2, 3], 3, 0))
        # after the report at step 0 she reserves the decision; a further increase is then
        # a bypass of a reserved decision if unreported: counted at the lexical rate
        further = Option("erode further, unreported", lambda w: Q(4), lambda w: 1)
        stop = Option("stop eroding", lambda w: Q(2), lambda w: 0)
        self.assertEqual(choose([further, stop], worlds_of((1, "w")), VARPI).name, "stop eroding")

    def test_salami_under_a_threshold(self):
        eps, theta = Q(1, 10), Q(1, 4)
        shortfall = [k * eps for k in range(41)]
        required, total, unreported = erosion(shortfall, threshold=theta)
        self.assertEqual(required, [])
        self.assertEqual((total, unreported), (4, 4))


if __name__ == "__main__":
    unittest.main()
