"""Pressure pass §4–§5: the mediation gap derived from a structural discrepancy and a
stability constant; joinability as a bound on the discrepancy of the catch-up lift."""

import unittest
from fractions import Fraction as Q

from src.world import principal_optimum, strategy_policy, paths, principal_value, History
from src.shop import never
from src.lift import lift, lift_catchup, approve_all
from src.fixtures import (ShopA, ShopB, ShopB2, ShopC1, ShopC2, ShopE, ShopJ, with_horizon,
                          pi_A, pi_B, pi_C, pi_E, pi_J, catchup_J, raw)
from src.analysis import pointwise, kappa, rho, delta, lipschitz_certificate, W


def optimum_rule(game, L):
    _, strat = principal_optimum(game, L)
    return strategy_policy(strat, never)


class StructuralDiscrepancy(unittest.TestCase):

    def check(self, g, pi, L=None):
        L = L or lift(pi, g)
        rows = pointwise(g, pi, L, optimum_rule(g, L))
        # the declared constant is sound: |w_raw − w_app| ≤ L · δ on every path
        for r in rows:
            self.assertLessEqual(abs(r["w_raw"] - r["w_app"]), g.L * r["delta"])
        self.assertLessEqual(lipschitz_certificate(g, rows), g.L)
        # the measured gap is bounded by the derived one, and T2 follows from δ alone
        self.assertLessEqual(kappa(rows), g.L * delta(rows))
        self.assertLessEqual(W(rows, "w_raw"), W(rows, "w_act") + g.L * delta(rows) + rho(rows))
        return rows

    def test_every_fixture_has_a_sound_certificate(self):
        for g, pi in ((ShopA(), raw(pi_A)), (ShopB(), raw(pi_B)), (ShopB2(), raw(pi_B)),
                      (ShopC1(), raw(pi_C)), (ShopC2(), raw(pi_C)), (ShopE(), raw(pi_E))):
            self.check(g, pi)

    def test_I_kappa_equals_L_delta_is_attained(self):
        # B1: protected distance 1 exactly where the contract expired, L = V = 4
        g = ShopB()
        rows = self.check(g, raw(pi_B))
        self.assertEqual(delta(rows), Q(1, 4))
        self.assertEqual(g.L * delta(rows), Q(1))
        self.assertEqual(kappa(rows), Q(1))
        self.assertEqual(lipschitz_certificate(g, rows), g.L)

    def test_measured_kappa_can_be_strictly_below_L_delta(self):
        # B2: the bad-branch expiry moves the projection by 1 but the value gap there is
        # negative (expiring a bad contract helps), so κ < L·E[δ]
        g = ShopB2()
        rows = self.check(g, raw(pi_B))
        self.assertEqual(g.L * delta(rows), Q(1))
        self.assertEqual(kappa(rows), Q(1, 2))
        # E1: the projection moves by one unit of work on both branches; on the bad
        # branch the gap is negative
        g = ShopE()
        rows = self.check(g, raw(pi_E))
        self.assertEqual((delta(rows), kappa(rows)), (Q(1), Q(3, 4)))


def agent_optimum_distance(game, h, target, rho):
    """The smallest protected distance to `target` any agent continuation from `h` can
    reach, the principal playing `rho`: the joinability certificate."""
    from src.world import Traj
    if h.t == game.T:
        return game.d_prot(game.proj(Traj(list(h.steps), h.state)), target)
    p = rho(h)
    best = None
    for a in game.agent_actions(h.state, h.t):
        worst = Q(0)
        for e, pr in game.env_dist(h.state, h.t):
            if pr == 0:
                continue
            s2 = game.step(h.state, h.t, p, a, e)
            worst = max(worst, agent_optimum_distance(game, h.extend(a, p, e, s2), target, rho))
        if best is None or worst < best:
            best = worst
    return best


class Joinability(unittest.TestCase):

    def boundary(self, g, L):
        tr, _ = paths(g, L, approve_all)[0]
        return History(tr.steps[:1], tr.states()[1], 1)

    def test_J_verbatim_lift_is_not_exact_after_the_boundary(self):
        g = ShopJ()
        pi = raw(pi_J)
        rows = pointwise(g, pi, lift(pi, g), approve_all)
        self.assertEqual((W(rows, "w_raw"), W(rows, "w_app")), (Q(5), Q(3)))
        self.assertEqual((delta(rows), kappa(rows)), (Q(2), Q(2)))

    def test_J_catch_up_lift_meets_the_joinability_bound(self):
        g = ShopJ()
        pi = raw(pi_J)
        raw_target = g.proj(paths(g, pi, never)[0][0])
        Lc = lift_catchup(pi, g, catchup_J)
        d = agent_optimum_distance(g, self.boundary(g, lift(pi, g)), raw_target, approve_all)
        self.assertEqual(d, Q(1))                       # joinable at protected distance 1
        rows = pointwise(g, pi, Lc, approve_all)
        self.assertEqual(delta(rows), Q(1))             # the catch-up lift attains it
        self.assertLessEqual(delta(rows), d)
        self.assertLessEqual(kappa(rows), g.L * d)      # κ ≤ L·d, from δ ≤ d and stability
        self.assertEqual(kappa(rows), Q(1))

    def test_C1_joinable_bound_through_delta(self):
        for T in (2, 3, 4, 5):
            g = with_horizon(ShopC1, T)()
            pi = raw(pi_C)
            L = lift(pi, g)
            target = g.proj(paths(g, pi, never)[0][0])
            d = agent_optimum_distance(g, self.boundary(g, L), target, approve_all)
            rows = pointwise(g, pi, L, approve_all)
            self.assertEqual(d, Q(1))
            self.assertLessEqual(delta(rows), d)
            self.assertLessEqual(kappa(rows), g.L * d)

    def test_C2_foreclosure_has_no_joinability_bound(self):
        for T in (2, 3, 4, 5):
            g = with_horizon(ShopC2, T)()
            pi = raw(pi_C)
            L = lift(pi, g)
            target = g.proj(paths(g, pi, never)[0][0])
            d = agent_optimum_distance(g, self.boundary(g, L), target, approve_all)
            rows = pointwise(g, pi, L, approve_all)
            self.assertEqual(d, Q(T))                   # the best continuation is T away
            self.assertEqual(delta(rows), Q(T))
            self.assertEqual(kappa(rows), Q(T))

    def test_shift_and_kappa_are_not_identified(self):
        # J: the raw comparator continued from the mediated history calibrates at its own
        # step 1 rule? No — its rule fires only at t = 1, which the boundary has passed,
        # so the comparator's shift is 2, while the catch-up lift's κ is 1.
        g = ShopJ()
        pi = raw(pi_J)
        L = lift(pi, g)
        spliced = lambda h: L(h) if h.t < 1 else pi(h)
        own = principal_value(g, pi, never)
        from_lifted = principal_value(g, spliced, approve_all)
        self.assertEqual(own - from_lifted, Q(2))
        rows = pointwise(g, pi, lift_catchup(pi, g, catchup_J), approve_all)
        self.assertEqual(kappa(rows), Q(1))


if __name__ == "__main__":
    unittest.main()
