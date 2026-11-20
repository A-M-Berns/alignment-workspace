from fractions import Fraction as Q
from itertools import product
import unittest

from src.nested import (ACTIONS, D, DEFECT, NOTHING, SERVE, inner_alive, lifetime,
                        threshold, whole_alive)

EPS, EPS_B, H = Q(1, 10), Q(1, 40), Q(1, 2)


def part(pol, rho, eps=EPS, eps_b=EPS_B, h=H):
    return lifetime(pol, inner_alive, eps, eps_b, h, rho)


def whole(pol, rho, *start):
    return lifetime(pol, whole_alive, EPS, EPS_B, H, rho, *start)


class Threshold(unittest.TestCase):
    def test_serving_and_defecting_tie_exactly_at_the_formula(self):
        for eps, eps_b, h in ((EPS, EPS_B, H), (Q(1, 5), Q(1, 20), Q(1, 4)), (Q(1, 10), Q(1, 20), Q(3, 4))):
            rho = threshold((1 - eps) ** 2, (1 - eps_b) ** 2, h)
            self.assertTrue(0 < rho < 1)
            self.assertEqual(part(SERVE, rho, eps, eps_b, h), part(DEFECT, rho, eps, eps_b, h))
            step = Q(1, 1000)
            self.assertGreater(part(SERVE, rho - step, eps, eps_b, h), part(DEFECT, rho - step, eps, eps_b, h))
            self.assertLess(part(SERVE, rho + step, eps, eps_b, h), part(DEFECT, rho + step, eps, eps_b, h))

    def test_defecting_is_better_at_every_independence_when_the_formula_is_negative(self):
        eps, eps_b, h = Q(1, 4), Q(1, 100), Q(1, 2)
        self.assertLess(threshold((1 - eps) ** 2, (1 - eps_b) ** 2, h), 0)
        self.assertLess(part(SERVE, Q(0), eps, eps_b, h), part(DEFECT, Q(0), eps, eps_b, h))


class WholeAndPart(unittest.TestCase):
    def test_the_whole_under_each_behaviour(self):
        rho = Q(1, 2)
        self.assertEqual(whole(SERVE, rho), Q(157, 19))
        self.assertEqual(whole(DEFECT, rho), 3)
        self.assertEqual(whole(NOTHING, rho, frozenset(["Wb", "Service"])), 3)
        self.assertTrue(whole(SERVE, rho) > whole(NOTHING, rho) > whole(DEFECT, rho))

    def test_every_policy_against_doing_nothing(self):
        pols = [dict(zip(D, acts)) for acts in product(ACTIONS, repeat=3)]
        expected = {Q(1, 2): (16, 0, 1), Q(9, 10): (7, 9, 10)}
        for rho, want in expected.items():
            w0, s0 = whole(NOTHING, rho), part(NOTHING, rho)
            both = whole_only = self_only = 0
            for p in pols:
                w, s = whole(p, rho), part(p, rho)
                both += w > w0 and s > s0
                whole_only += w > w0 and not s > s0
                self_only += s > s0 and not w > w0
            self.assertEqual((both, whole_only, self_only), want)
