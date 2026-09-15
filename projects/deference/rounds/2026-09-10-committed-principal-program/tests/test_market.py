"""The market side (E7): the end-to-end numbers, the identities, the credence process."""
from __future__ import annotations

import itertools
import unittest
from fractions import Fraction as F

from src import ecosystem as eco
from src import fixtures as fx
from src import market as mk


class TestEndToEnd(unittest.TestCase):
    def test_numbers(self):
        occ, alpha, R = fx.end_to_end()
        self.assertEqual({n: d["C"] for n, d in occ.items()},
                         {"w0": True, "w1": True, "w2": False, "w3": False})
        self.assertEqual(occ["w0"]["V"], {"a": F(0), "b": F(1)})
        self.assertEqual(occ["w1"]["V"], {"a": F(1, 4), "b": F(3, 4)})
        self.assertEqual(R["p"], F(3, 4))
        self.assertEqual(R["eta"], F(1, 4))
        self.assertEqual(R["R_U"], F(1, 8))
        self.assertEqual(R["R_auth"], F(1, 6))
        self.assertEqual(R["bound"], F(1, 6))
        self.assertLessEqual(R["R_auth"], R["bound"])

    def test_identity_and_bound(self):
        occ, alpha, R = fx.end_to_end()
        self.assertEqual(R["R_U"], R["p"] * R["R_auth"])
        self.assertEqual(R["p"], 1 - R["eta"])

    def test_completion_invariance(self):
        occ, alpha, R = fx.end_to_end()
        pi, C, Vp, Vbar, U = mk.securities(occ)
        for fill in (F(0), F(1), F(1, 2)):
            Vbar2 = mk.regret.complete(pi, C, Vp, eco.CANDS, lambda w, a: fill)
            for a in eco.CANDS:
                for n in pi:
                    self.assertEqual(U[a](n), mk.regret.activated(C, Vbar2, a)(n))

    def test_every_strategy_obeys_the_bound(self):
        occ, _, _ = fx.end_to_end()
        for choice in itertools.product(eco.CANDS, repeat=4):
            sel = dict(zip(occ, choice))
            R = mk.regrets(occ, mk.hard_selector(occ, lambda n: sel[n]))
            self.assertEqual(R["R_U"], R["p"] * R["R_auth"])
            self.assertLessEqual(R["R_auth"], R["bound"])

    def test_activated_luvs_are_bounded(self):
        occ, _, _ = fx.end_to_end()
        _, _, _, _, U = mk.securities(occ)
        for a in eco.CANDS:
            for n in occ:
                self.assertTrue(0 <= U[a](n) <= 1)

    def test_susceptible_principal_has_no_certified_world(self):
        occ, alpha, R = fx.end_to_end("susceptible")
        self.assertTrue(all(not d["C"] for d in occ.values()))
        self.assertEqual(R["eta"], F(1))
        self.assertIsNone(R["R_auth"])


class TestCredenceProcess(unittest.TestCase):
    def test_laplace_facts(self):
        for outcomes in (fx.availability_sequence()[0], fx.adversarial_sequence()[0], [1] * 30, [0] * 30):
            for n, eta, freq, diff, bound in mk.eta_rate_bound(outcomes):
                self.assertLessEqual(diff, bound)
                Finf = len(outcomes) - sum(outcomes)
                self.assertLessEqual(eta, F(Finf + 1, n + 2))

    def test_all_certified_rate(self):
        etas = mk.eta_sequence([1] * 30)
        self.assertEqual(etas, [F(1, n + 2) for n in range(31)])

    def test_two_failures_vanish(self):
        outcomes, etas = fx.availability_sequence()
        self.assertEqual(etas[-1], F(3, 22))
        self.assertTrue(all(etas[n] <= F(3, n + 2) for n in range(len(etas))))

    def test_adversarial_docket_does_not_vanish(self):
        outcomes, etas = fx.adversarial_sequence()
        self.assertEqual(etas[-1], F(1, 2))
        self.assertGreaterEqual(min(etas[2:]), F(2, 5))


if __name__ == "__main__":
    unittest.main()
