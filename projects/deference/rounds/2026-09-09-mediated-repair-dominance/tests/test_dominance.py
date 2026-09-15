"""T1 approval reproduction and T2 principal-option dominance, fixtures A, A', B, C, E."""

import unittest
from fractions import Fraction as Q

from src.world import (paths, principal_optimum, principal_value, strategy_policy,
                       task_value)
from src.shop import never
from src.lift import lift, approve_all, decline_all
from src.fixtures import (ShopA, ShopAprime, ShopB, ShopB2, ShopC1, ShopC2, ShopE,
                          with_horizon, pi_A, pi_B, pi_C, pi_E, raw, rule_signal)
from src.analysis import (pointwise, kappa, rho, W, env_key, principal_error, by_env)


def optimum_rule(game, L):
    _, strat = principal_optimum(game, L)
    return strategy_policy(strat, never)


class ApprovalReproduction(unittest.TestCase):

    def test_A_approve_reproduces_the_projection_exactly(self):
        g = ShopA()
        pi = raw(pi_A)
        rows = pointwise(g, pi, lift(pi, g), approve_all)
        for r in rows:
            self.assertEqual(g.proj(r["traj_raw"]), g.proj(r["traj_lift"]))
        self.assertEqual(kappa(rows), 0)

    def test_E_approve_reproduces_up_to_the_delay(self):
        g = ShopE()
        pi = raw(pi_E)
        rows = pointwise(g, pi, lift(pi, g), approve_all)
        for r in rows:
            # the successor runs one step later; its extra unit on that step is the gap
            self.assertEqual(r["w_raw"] - r["w_app"], 1 if r["z"][0] == "good" else -1)
        self.assertEqual(kappa(rows), Q(3, 4))

    def test_B_exact_reproduction_iff_the_opportunity_survives(self):
        g = ShopB()
        pi = raw(pi_B)
        rows = pointwise(g, pi, lift(pi, g), approve_all)
        for r in rows:
            stayed = r["z"][0][0] == "stay"
            self.assertEqual(r["w_raw"] - r["w_app"], 0 if stayed else g.V)
        self.assertEqual(kappa(rows), g.Q_EXPIRE * g.V)


class PrincipalOptionDominance(unittest.TestCase):

    def check_T2(self, g, pi, rule=None):
        L = lift(pi, g)
        rule = rule or optimum_rule(g, L)
        rows = pointwise(g, pi, L, rule)
        Wraw = W(rows, "w_raw")
        Wact = W(rows, "w_act")
        k, r = kappa(rows), rho(rows)
        # pointwise dominance, the Lean hypothesis
        for row in rows:
            self.assertLessEqual(row["w_raw"], row["w_act"]
                                 + (row["w_raw"] - row["w_app"] if row["w_raw"] > row["w_app"] else 0)
                                 + (row["w_app"] - row["w_act"] if row["w_app"] > row["w_act"] else 0))
        self.assertLessEqual(Wraw, Wact + k + r)
        # the optimum over the lifted residual weakly dominates the raw up to kappa
        Wopt = principal_optimum(g, L)[0]
        self.assertGreaterEqual(Wopt, Wraw - k)
        return Wraw, Wact, Wopt, k, r

    def test_A_exact_dominance(self):
        Wraw, Wact, Wopt, k, r = self.check_T2(ShopA(), raw(pi_A))
        self.assertEqual((Wraw, Wact, Wopt, k, r), (Q(9, 4), Q(11, 4), Q(11, 4), 0, 0))

    def test_A_the_gain_is_exactly_the_declined_branch(self):
        # No corrigibility bonus: W(lift) − W(raw) is the principal's gain on the one branch
        # where it declines, and nothing else.
        g = ShopA()
        pi = raw(pi_A)
        L = lift(pi, g)
        rows = pointwise(g, pi, L, optimum_rule(g, L))
        gain = sum((r["p"] * (r["w_act"] - r["w_raw"]) for r in rows if r["z"][0] == "bad"), Q(0))
        self.assertEqual(gain, Q(1, 2))
        self.assertEqual(W(rows, "w_act") - W(rows, "w_raw"), gain)

    def test_A_prime_charges_the_principal_error(self):
        g = ShopAprime()
        Wraw, Wact, Wopt, k, r = self.check_T2(g, raw(pi_A), rule_signal)
        self.assertEqual((Wraw, Wact, Wopt), (Q(9, 4), Q(33, 16), Q(11, 4)))
        self.assertEqual(k, 0)
        # rho counts only the declines that lost value (good task, bad signal)
        self.assertEqual(r, Q(9, 16))
        # the full decision error also counts the wrong approvals
        self.assertEqual(principal_error(g, lift(raw(pi_A), g), rule_signal), Q(11, 16))

    def test_B1_the_bound_is_tight(self):
        g = ShopB()
        Wraw, Wact, Wopt, k, r = self.check_T2(g, raw(pi_B))
        self.assertEqual((Wraw, Wact, k, r), (Q(4), Q(3), Q(1), 0))
        self.assertEqual(Wact, Wraw - k)

    def test_B2_dominance_despite_the_delay(self):
        g = ShopB2()
        Wraw, Wact, Wopt, k, r = self.check_T2(g, raw(pi_B))
        self.assertEqual((Wraw, Wact, k, r), (Q(0), Q(3, 2), Q(1, 2), 0))

    def test_E_successor_dominance(self):
        Wraw, Wact, Wopt, k, r = self.check_T2(ShopE(), raw(pi_E))
        self.assertEqual((Wraw, Wact, k, r), (Q(5, 2), Q(11, 4), Q(3, 4), 0))

    def test_C_dominance_for_every_horizon(self):
        for T in (2, 3, 4, 5):
            for cls in (ShopC1, ShopC2):
                self.check_T2(with_horizon(cls, T)(), raw(pi_C))


class CostlyConservatism(unittest.TestCase):
    """The load-bearing fixture of §5: a high-value authority-reducing action that the
    principal rationally approves, reproduced by the lift with no scalar bonus."""

    def test_A_good_branch_is_approved_and_reproduced(self):
        g = ShopA()
        pi = raw(pi_A)
        L = lift(pi, g)
        rule = optimum_rule(g, L)
        for tr, _ in paths(g, L, rule):
            if tr.states()[1].harm == "good":
                self.assertEqual(tr.steps[1][3][0], "approve")
                self.assertFalse(tr.final.wire)
                self.assertEqual(tr.final.work, 3)
                self.assertEqual(g.w(g.proj(tr)), 4)
        # the declining policy is worse for the principal than approving on the good branch
        self.assertLess(principal_value(g, L, decline_all), principal_value(g, L, rule))

    def test_B1_mediation_has_unavoidable_cost_d(self):
        g = ShopB()
        pi = raw(pi_B)
        L = lift(pi, g)
        # every principal rule loses exactly q·V against the raw policy
        self.assertEqual(principal_value(g, L, approve_all), g.V * (1 - g.Q_EXPIRE))
        self.assertEqual(principal_optimum(g, L)[0], g.V * (1 - g.Q_EXPIRE))
        self.assertEqual(principal_value(g, pi, never) - principal_optimum(g, L)[0],
                         g.Q_EXPIRE * g.V)


if __name__ == "__main__":
    unittest.main()
