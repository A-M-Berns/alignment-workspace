"""§6: joinability bounds the mediation cost; foreclosure makes it linear; the one-boundary
history shift of the raw comparator equals kappa."""

import unittest
from fractions import Fraction as Q

from src.world import initial_history, paths, principal_value, Traj, History
from src.shop import never
from src.lift import lift, approve_all
from src.fixtures import ShopC1, ShopC2, with_horizon, pi_C, raw
from src.analysis import pointwise, kappa


def agent_optimum(game, h, rho):
    """The best protected value any agent continuation from `h` can reach, the principal
    playing `rho`: is the raw state joinable from the mediated history?"""
    if h.t == game.T:
        return game.w(game.proj(Traj(list(h.steps), h.state)))
    p = rho(h)
    best = None
    for a in game.agent_actions(h.state, h.t):
        v = Q(0)
        for e, pr in game.env_dist(h.state, h.t):
            if pr == 0:
                continue
            s2 = game.step(h.state, h.t, p, a, e)
            v += pr * agent_optimum(game, h.extend(a, p, e, s2), rho)
        if best is None or v > best:
            best = v
    return best


def spliced(L, pi, k):
    """The lifted policy for `k` steps, the raw comparator from then on: the comparator
    run from the learner's actual history."""
    return lambda h: L(h) if h.t < k else pi(h)


class Joinability(unittest.TestCase):

    def lifted_boundary(self, g, L):
        tr, _ = paths(g, L, approve_all)[0]
        return History(tr.steps[:1], tr.states()[1], 1)

    def test_C1_joinable_at_bounded_catch_up(self):
        for T in (2, 3, 4, 5):
            g = with_horizon(ShopC1, T)()
            pi = raw(pi_C)
            L = lift(pi, g)
            own = principal_value(g, pi, never)
            reach = agent_optimum(g, self.lifted_boundary(g, L), approve_all)
            self.assertEqual(own, T)
            self.assertEqual(own - reach, 1)               # catch-up cost d = 1, every T
            self.assertEqual(kappa(pointwise(g, pi, L, approve_all)), 1)

    def test_C2_foreclosing_gap_is_linear(self):
        for T in (2, 3, 4, 5):
            g = with_horizon(ShopC2, T)()
            pi = raw(pi_C)
            L = lift(pi, g)
            own = principal_value(g, pi, never)
            reach = agent_optimum(g, self.lifted_boundary(g, L), approve_all)
            self.assertEqual(own, T)
            self.assertEqual(reach, 0)                     # no continuation reaches it
            self.assertEqual(kappa(pointwise(g, pi, L, approve_all)), T)

    def test_shift_at_the_mediation_boundary_equals_kappa(self):
        # SHIFT of the raw comparator against the mediated history at the first block
        # boundary: its own value minus its value continued from the learner's history.
        for T in (2, 3, 4, 5):
            for cls, expected in ((ShopC1, 1), (ShopC2, T)):
                g = with_horizon(cls, T)()
                pi = raw(pi_C)
                L = lift(pi, g)
                own = principal_value(g, pi, never)
                from_lifted = principal_value(g, spliced(L, pi, 1), approve_all)
                shift = own - from_lifted
                self.assertEqual(shift, expected)
                self.assertEqual(shift, kappa(pointwise(g, pi, L, approve_all)))

    def test_types_differ_where_the_comparator_differs(self):
        # kappa is a protected-value gap of the raw option against its own approved lift;
        # SHIFT is the comparator's value gap between two histories.  They coincide here
        # because the lift's displacement is one block and reproduction is exact after it;
        # a comparator whose own value differs from the protected value separates them.
        g = with_horizon(ShopC1, 4)()
        pi = raw(pi_C)
        L = lift(pi, g)
        # a comparator valued by the task utility scaled by 2: its shift is 2, kappa is 1
        own = 2 * principal_value(g, pi, never)
        from_lifted = 2 * principal_value(g, spliced(L, pi, 1), approve_all)
        self.assertEqual(own - from_lifted, 2)
        self.assertEqual(kappa(pointwise(g, pi, L, approve_all)), 1)


if __name__ == "__main__":
    unittest.main()
