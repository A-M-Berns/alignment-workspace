"""The finite compilation: gated products are single variables, validity in every world,
credence independence, and the soft selector on bounded, growing and tied menus."""

import unittest
from fractions import Fraction as Q

from src import compile as C

L, D, DMAX = Q(4), Q(8), Q(1)


def world(c_raw, c_corr, w_raw, w_app, w_act, delta):
    return {"c_raw": bool(c_raw), "c_corr": bool(c_corr), "w_raw": Q(w_raw),
            "w_app": Q(w_app), "w_act": Q(w_act), "delta": Q(delta)}


WORLDS = [
    world(1, 1, 8, 8, 4, 0),      # common activation, exact reproduction, decline regret 4
    world(1, 1, 8, 4, 4, 1),      # common activation, discrepancy 1 at L = 4
    world(1, 0, 8, 8, 8, 0),      # raw-only activation: the mismatch branch
    world(0, 1, 8, 8, 8, 0),      # corr-only activation: free
    world(0, 0, 8, 8, 8, 0),      # void for both
    world(1, 1, 0, 0, 8, 0),      # the principal improves on the raw policy
]


class Compilation(unittest.TestCase):

    def test_gated_product_is_one_variable(self):
        for w in WORLDS:
            v = C.luvs(w, L, D, DMAX)
            both = w["c_raw"] and w["c_corr"]
            self.assertEqual(v["G_delta"], (Q(1) if both else Q(0)) * w["delta"] / DMAX)
            self.assertEqual(v["U_raw"], (Q(1) if w["c_raw"] else Q(0)) * w["w_raw"] / D)
            for k in v:
                self.assertTrue(Q(0) <= v[k] <= Q(1))

    def test_valid_in_every_world(self):
        for w in WORLDS:
            self.assertTrue(C.in_range(w, D, DMAX))
            self.assertTrue(C.certified(w, L))
        self.assertTrue(C.valid_everywhere(WORLDS, L, D, DMAX))

    def test_uncertified_world_breaks_validity(self):
        # a world where the approve branch does not reproduce the raw value within L·δ
        bad = world(1, 1, 8, 0, 0, 0)
        self.assertFalse(C.certified(bad, L))
        self.assertGreater(C.constraint(bad, L, D, DMAX), 0)

    def test_credence_independence(self):
        credences = [
            [Q(1, 6)] * 6,
            [Q(1), Q(0), Q(0), Q(0), Q(0), Q(0)],
            [Q(0), Q(0), Q(1, 2), Q(1, 2), Q(0), Q(0)],
            [Q(1, 10), Q(2, 10), Q(3, 10), Q(4, 10), Q(0), Q(0)],
        ]
        for mu in credences:
            self.assertLessEqual(C.expectation(mu, WORLDS, lambda w: C.constraint(w, L, D, DMAX)), 0)

    def test_coefficients_bounded(self):
        self.assertEqual(C.coefficient_l1(L, D, DMAX), Q(3) + Q(1, 2))

    def test_mismatch_branch_attains_zero(self):
        self.assertEqual(C.constraint(WORLDS[2], L, D, DMAX), Q(0))
        self.assertEqual(C.constraint(WORLDS[0], L, D, DMAX), Q(0))
        self.assertEqual(C.constraint(WORLDS[1], L, D, DMAX), Q(0))


class SoftSelector(unittest.TestCase):

    def check(self, scores, delta):
        w = C.soft_weights(scores, delta)
        self.assertTrue(all(x >= 0 for x in w))
        self.assertEqual(sum(w, Q(0)), Q(1))
        self.assertTrue(C.support_near_max(scores, w, delta))
        self.assertLessEqual(max(scores) - 2 * delta, C.aggregate(scores, w))
        return w

    def test_bounded_menu(self):
        self.check([Q(-1, 3), Q(1, 5), Q(-2), Q(1, 7)], Q(1, 10))

    def test_ties(self):
        w = self.check([Q(1, 2), Q(1, 2), Q(-1)], Q(1, 10))
        self.assertEqual(w[0], w[1])
        self.assertEqual(w[2], Q(0))

    def test_growing_menu(self):
        # menu size n², window 1/n: the aggregate is within 2/n of the maximum
        for n in range(1, 8):
            scores = [Q((-1) ** q * q, n * n + q + 1) for q in range(n * n)]
            delta = Q(1, n)
            w = self.check(scores, delta)
            self.assertLessEqual(max(scores), C.aggregate(scores, w) + 2 * delta)

    def test_hard_argmax_is_discontinuous(self):
        eps = Q(1, 10 ** 6)
        a = [Q(1), Q(1) - eps]
        b = [Q(1) - eps, Q(1)]
        dist, flipped = C.hard_selector_jump(a, b)
        self.assertEqual(dist, eps)
        self.assertTrue(flipped)
        # the soft weights move continuously: within eps/δ of each other
        wa, wb = C.soft_weights(a, Q(1, 10)), C.soft_weights(b, Q(1, 10))
        self.assertLessEqual(max(abs(x - y) for x, y in zip(wa, wb)), eps / Q(1, 10))

    def test_convex_combination_valid_in_every_world(self):
        pairs = [WORLDS, list(reversed(WORLDS)), WORLDS[2:] + WORLDS[:2]]
        scores = [Q(1, 3), Q(-1, 2), Q(1, 4)]
        w = C.soft_weights(scores, Q(1, 8))
        for i in range(len(WORLDS)):
            self.assertLessEqual(C.convex_constraint(pairs, w, L, D, DMAX, i), 0)


if __name__ == "__main__":
    unittest.main()
