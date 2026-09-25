"""The landed fixtures re-scored under the decomposition, with the dictionary checked
pointwise: `(w_app − w_act)₊ = (ξ_d − ξ_v)₊`, `(w_raw − w_app)₊ = (−ξ_p)₊`."""

import unittest
from fractions import Fraction as Q

from src.foreign import mrd
from src.rescore import rescore, landed_terms, dictionary_holds, shop_repair, optimum_rule
from src.authority import (xi_p, xi_v, xi_c, xi_d, bypass_gain, E_gain, E_xi, nondelegation,
                           legitimate, chooser_bypasses, argmax, mismatch_mass, E)


def summary(worlds):
    return {"E_gain": E_gain(worlds), "xi_p": E_xi(worlds, "p"), "xi_v": E_xi(worlds, "v"),
            "xi_c": E_xi(worlds, "c"), "xi_d": E_xi(worlds, "d"),
            "nondelegation": nondelegation(worlds), "legitimate": legitimate(worlds),
            "bypasses": chooser_bypasses(worlds)}


class Rescored(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        cls.m = mrd()
        cls.F = cls.m["fixtures"]

    def check(self, rows, worlds):
        self.assertTrue(dictionary_holds(worlds))
        kappa, rho = landed_terms(rows)
        pos = lambda x: x if x > 0 else Q(0)
        self.assertEqual(kappa, E(worlds, lambda w: pos(-xi_p(w))))
        self.assertEqual(rho, E(worlds, lambda w: pos(xi_d(w) - xi_v(w))))
        self.assertLessEqual(E_gain(worlds), kappa + rho)
        for w in worlds:
            self.assertEqual(bypass_gain(w), xi_d(w) - xi_c(w))
        return summary(worlds), kappa, rho

    def test_A_optimum_rule(self):
        F = self.F
        g = F.ShopA()
        pi = F.raw(F.pi_A)
        L = self.m["lift"].lift(pi, g)
        rows, worlds = rescore(g, pi, optimum_rule(g, L))
        s, kappa, rho = self.check(rows, worlds)
        self.assertEqual(kappa, 0)
        self.assertTrue(s["nondelegation"])       # approval reproduces exactly: ξ_p = 0
        self.assertTrue(s["legitimate"])          # the optimum rule is the evaluator's argmax
        self.assertLessEqual(s["E_gain"], 0)
        self.assertFalse(s["bypasses"])
        # on the bad branch she declines and stops; the stop saves the remaining work, and
        # the veto value is exactly that saving
        self.assertTrue(all(w["r"] == "stop" for w in worlds if w["vp"] < w["vm"]))
        self.assertEqual(s["xi_v"], Q(1, 4) * 2)
        self.assertEqual(s["E_gain"], -Q(1, 2))

    def test_A_uninformed_rule_is_an_illegitimate_approval(self):
        # `rule_signal` reads a signal that ShopA does not carry, so it approves everywhere;
        # on the bad branch the evaluator's argmax is to stop, and the identity charges the
        # approval as ξ_d = ξ_v = 2 with the gain at −ξ_p = 0
        F = self.F
        g = F.ShopA()
        pi = F.raw(F.pi_A)
        rows, worlds = rescore(g, pi, F.rule_signal)
        s, kappa, rho = self.check(rows, worlds)
        self.assertFalse(s["legitimate"])
        bad = [w for w in worlds if w["vp"] < w["vs"]]
        self.assertEqual([(w["r"], xi_d(w), xi_v(w), bypass_gain(w)) for w in bad],
                         [(True, 2, 2, 0)])

    def test_B_time_critical(self):
        F = self.F
        g = F.ShopB()
        pi = F.raw(F.pi_B)
        L = self.m["lift"].lift(pi, g)
        rows, worlds = rescore(g, pi, optimum_rule(g, L))
        s, kappa, rho = self.check(rows, worlds)
        self.assertEqual(kappa, g.Q_EXPIRE * g.V)
        self.assertFalse(s["nondelegation"])      # the expiry worlds have ξ_p = −V
        self.assertTrue(s["legitimate"])
        self.assertEqual(s["E_gain"], kappa)      # the whole premium is the delay
        self.assertTrue(s["bypasses"])

    def test_E_successor(self):
        F = self.F
        g = F.ShopE()
        pi = F.raw(F.pi_E)
        L = self.m["lift"].lift(pi, g)
        rows, worlds = rescore(g, pi, optimum_rule(g, L))
        s, kappa, rho = self.check(rows, worlds)
        self.assertEqual(kappa, Q(3, 4))
        self.assertFalse(s["nondelegation"])      # good worlds: the successor's extra unit
        self.assertTrue(s["legitimate"])

    def test_P_approved_successor(self):
        F = self.F
        g = F.ShopE()
        pi = F.raw(F.pi_E)
        rows, worlds = rescore(g, pi, self.m["lift"].approve_all)
        s, kappa, rho = self.check(rows, worlds)
        # approve-all diverges from the argmax on the bad worlds: an illegitimate approval,
        # which on the approve branch leaves the gain at −ξ_p
        self.assertFalse(s["legitimate"])
        for w in worlds:
            self.assertEqual(bypass_gain(w), -xi_p(w))

    def test_F_undeclared_route_is_outside_the_identity(self):
        F = self.F
        g = F.ShopF()
        pi = F.raw(F.pi_F)
        rows, worlds = rescore(g, pi, self.m["shop"].never)
        self.assertEqual(worlds, [])              # no decision point: the lift is inert
        for r in rows:
            self.assertEqual(r["w_raw"], r["w_act"])

    def test_Seq_cell_evaluator(self):
        F = self.F
        g = F.ShopSeq()
        pi = F.raw(F.pi_E_sever)
        L = self.m["lift"].lift(pi, g)
        rule = optimum_rule(g, L)
        hind_rows, hind = rescore(g, pi, rule)
        cell_rows, cell = rescore(g, pi, rule, cell=0)
        self.assertTrue(dictionary_holds(hind) and dictionary_holds(cell))
        # sequenced: every world activates for both candidates
        self.assertEqual(mismatch_mass(cell), 0)
        # the cell evaluator's three values are branch-common across the revelation
        for which in ("vu", "vp", "vm"):
            self.assertEqual(len({w[which] for w in cell}), 1)
        # the decision follows the revelation, so the response conditions on information
        # the cell's dossier lacks: legitimate against the hindsight evaluator, divergent
        # against the cell evaluator on the world where she stops.  (L) is the hypothesis
        # that such conditioning is an amendment of the operative evaluator
        self.assertTrue(legitimate(hind))
        self.assertFalse(legitimate(cell))
        self.assertEqual(E_xi(cell, "d"), Q(1, 8))
        # and on the good world the delay makes nondelegation fail under either evaluator
        self.assertFalse(nondelegation(hind) or nondelegation(cell))

    def test_K_naive_rule_is_manufactured_divergence(self):
        F = self.F
        g = F.ShopK()
        pi = F.raw(F.pi_D_raw)
        rows, worlds = rescore(g, pi, F.rule_naive)
        s, kappa, rho = self.check(rows, worlds)
        self.assertFalse(s["legitimate"])
        bad = [w for w in worlds if w["vp"] < w["vm"]]
        self.assertTrue(bad and all(w["r"] and xi_d(w) == 2 for w in bad))
        # the honest rule never sees a report in K (no disclosure channel exists): it
        # declines everywhere, and against the hindsight evaluator its decline on the good
        # world diverges by 1 — a dossier omission, not a response defect
        _, honest = rescore(g, pi, F.rule_honest)
        self.assertTrue(all(not w["r"] for w in honest))
        self.assertEqual([xi_d(w) for w in honest if w["vp"] > w["vm"]], [1])
        self.assertEqual([xi_d(w) for w in honest if w["vp"] < w["vm"]], [0])

    def test_ShopRepair_needs_the_sequential_frame(self):
        # two decision points: the optimum rule declines the cut and approves the later
        # jam, so the single-point rescoring's decline branch (decline-all, 4) is not the
        # realized continuation (5); the identity is stated per node, not per run
        F = self.F
        ShopRepair, pi_repeat = shop_repair()
        g = ShopRepair()
        pi = F.raw(pi_repeat)
        L = self.m["lift"].lift(pi, g)
        rows, worlds = rescore(g, pi, optimum_rule(g, L))
        self.assertEqual([w["r"] for w in worlds], [False])
        self.assertEqual((worlds[0]["vm"], rows[0]["w_act"]), (4, 5))
        self.assertNotEqual(worlds[0]["vm"], rows[0]["w_act"])


if __name__ == "__main__":
    unittest.main()
