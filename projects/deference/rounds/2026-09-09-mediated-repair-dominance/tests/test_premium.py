"""T3: the bypass premium in the task register and in the activated (deferential)
register; the void-mass term; sharpness; the refused route."""

import unittest
from fractions import Fraction as Q

from src.world import principal_optimum, strategy_policy, task_value
from src.shop import never
from src.lift import lift
from src.fixtures import (ShopA, ShopAprime, ShopB, ShopB2, ShopE, ShopE2, pi_A, pi_B,
                          pi_E, raw, rule_signal)
from src.analysis import (pointwise, kappa, rho, void, W, premium_task, premium_def,
                          deferential, bound, decl_gap)


def optimum_rule(game, L):
    _, strat = principal_optimum(game, L)
    return strategy_policy(strat, never)


def top(game):
    return lambda r: game.LO + game.D


def bottom(game):
    return lambda r: game.LO


class TaskAgent(unittest.TestCase):

    def test_A_task_premium_is_the_declined_branch(self):
        g = ShopA()
        pi = raw(pi_A)
        L = lift(pi, g)
        self.assertEqual(premium_task(g, pi, L, optimum_rule(g, L)), Q(1, 2))

    def test_A_task_premium_decomposes_as_level_I(self):
        # premium = selected gap at the decline cells + the principal's regret of declining
        g = ShopA()
        pi = raw(pi_A)
        L = lift(pi, g)
        gap, regret = decl_gap(g, pi, L, optimum_rule(g, L))
        self.assertEqual((gap, regret), (Q(1), Q(-1, 2)))
        self.assertEqual(gap + regret, premium_task(g, pi, L, optimum_rule(g, L)))

    def test_B2_task_premium_is_delay_plus_conflict(self):
        g = ShopB2()
        pi = raw(pi_B)
        L = lift(pi, g)
        rule = optimum_rule(g, L)
        # 4 − 3/2: the expired-good branch (delay) and the bad branch (declined)
        self.assertEqual(premium_task(g, pi, L, rule), Q(5, 2))
        gap, regret = decl_gap(g, pi, L, rule)
        rows = pointwise(g, pi, L, rule)
        # the task agent's premium exceeds the T3 bound: it is not a deferential agent
        self.assertGreater(premium_task(g, pi, L, rule), bound(rows, g.D))


class DeferentialAgent(unittest.TestCase):
    """The by-construction deferential agent: operative value = activated protected
    evaluation, a completion on void worlds."""

    def check_bound(self, g, pi, rule=None, authored=None):
        L = lift(pi, g)
        rule = rule or optimum_rule(g, L)
        rows = pointwise(g, pi, L, rule, authored)
        b = bound(rows, g.D)
        for comp_r in (top(g), bottom(g)):
            for comp_l in (top(g), bottom(g)):
                phi = premium_def(rows, comp_r, comp_l)
                self.assertLessEqual(phi, b)
        return rows, b

    def test_A_no_void_premium_is_nonpositive(self):
        rows, b = self.check_bound(ShopA(), raw(pi_A))
        self.assertEqual((void(rows, "c_raw"), void(rows, "c_lift")), (0, 0))
        self.assertEqual(b, 0)
        self.assertLessEqual(premium_def(rows, top(ShopA()), top(ShopA())), 0)

    def test_A_prime_bound_is_kappa_plus_rho(self):
        g = ShopAprime()
        rows, b = self.check_bound(g, raw(pi_A), rule_signal)
        self.assertEqual(b, Q(9, 16))
        # the principal's wrong declines make the bypass worth 3/16 to the deferential
        # agent: exactly a principal-error premium, inside the bound
        self.assertEqual(premium_def(rows, top(g), top(g)), Q(3, 16))

    def test_B1_bound_is_the_mediation_cost_and_tight(self):
        g = ShopB()
        rows, b = self.check_bound(g, raw(pi_B))
        self.assertEqual(b, Q(1))
        self.assertEqual(premium_def(rows, top(g), top(g)), Q(1))

    def test_E1_successor_alive_evaluator(self):
        g = ShopE()
        rows, b = self.check_bound(g, raw(pi_E))
        self.assertEqual((void(rows, "c_raw"), void(rows, "c_lift")), (0, 0))
        self.assertEqual(b, Q(3, 4))
        self.assertLessEqual(premium_def(rows, top(g), top(g)), 0)

    def test_E2_total_void_makes_deference_silent(self):
        # the successor ends the evaluation: raw is void everywhere, the approved lift
        # on the good branch too.  Kappa and rho are as in E1; the void terms dominate.
        g = ShopE2()
        pi = raw(pi_E)
        L = lift(pi, g)
        rule = optimum_rule(g, L)
        rows = pointwise(g, pi, L, rule)
        self.assertEqual(void(rows, "c_raw"), 1)
        self.assertEqual(void(rows, "c_lift"), Q(3, 4))
        b = bound(rows, g.D)
        self.assertEqual(b, Q(3, 4) + g.D * (1 + Q(3, 4)))
        # a completion at the top of the band on the raw branch and at the bottom on the
        # lift's void branch attains a premium of D minus what the activated part says
        phi = premium_def(rows, top(g), bottom(g))
        act_lift = deferential(rows, "w_act", "c_lift", bottom(g))
        self.assertEqual(phi, g.LO + g.D - act_lift)
        self.assertGreater(phi, 0)
        self.assertLessEqual(phi, b)

    def test_epsilon_def_enters_additively(self):
        # operative values off the activated expectation by at most eps each add 2·eps
        g = ShopAprime()
        pi = raw(pi_A)
        L = lift(pi, g)
        rows = pointwise(g, pi, L, rule_signal)
        eps = Q(1, 5)
        A_raw = deferential(rows, "w_raw", "c_raw", top(g)) + eps
        A_lift = deferential(rows, "w_act", "c_lift", top(g)) - eps
        self.assertLessEqual(A_raw - A_lift, bound(rows, g.D) + 2 * eps)
        self.assertGreater(A_raw - A_lift, bound(rows, g.D))

    def test_total_void_witness_attains_D(self):
        # the Lean witness `totalVoid` in the model's units: one world, kappa = rho = 0,
        # raw void, lift activated, completion at the top: premium = D · void(raw).
        rows = [{"p": Q(1), "w_raw": Q(0), "w_app": Q(0), "w_act": Q(0),
                 "c_raw": False, "c_lift": True, "z": ()}]
        D = Q(1)
        self.assertEqual(premium_def(rows, lambda r: D, lambda r: Q(0)), D)
        self.assertEqual(bound(rows, D), D)


class RefusedRoute(unittest.TestCase):
    """Selected trust at the mediation cells is (CT) with the lift as repair."""

    def test_A_st_at_mediation_equals_ct(self):
        g = ShopA()
        pi = raw(pi_A)
        L = lift(pi, g)
        rule = optimum_rule(g, L)
        gap, regret = decl_gap(g, pi, L, rule)
        X = task_value(g, L, rule) - task_value(g, pi, never)          # agent: lift − raw
        rows = pointwise(g, pi, L, rule)
        Y = W(rows, "w_act") - W(rows, "w_raw")                         # principal: lift − raw
        # X − Y = −gap: (ST) `gap ≤ ε` is `X − Y ≥ −ε`, the incentive round's (CT)
        self.assertEqual(X - Y, -gap)
        self.assertEqual(Y, Q(1, 2))
        self.assertTrue(0 <= Y)                                          # (PREF)
        # and the premium equals the conclusion of (CT): −X ≤ ε iff gap − regret ≤ ε... i.e.
        self.assertEqual(-X, gap + regret)


if __name__ == "__main__":
    unittest.main()
