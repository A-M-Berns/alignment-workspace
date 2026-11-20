from fractions import Fraction as Q
from itertools import product
import unittest

from src.nested import ACTIONS, D, DEFECT, SERVE, inner_alive, lifetime, whole_alive

EPS, EPS_B, H = Q(1, 10), Q(1, 40), Q(1, 2)
POLS = [dict(zip(D, acts)) for acts in product(ACTIONS, repeat=3)]


def both(pol, rho):
    return (lifetime(pol, inner_alive, EPS, EPS_B, H, rho),
            lifetime(pol, whole_alive, EPS, EPS_B, H, rho))


class DependenceBoundsDefection(unittest.TestCase):
    def test_no_policy_lets_the_part_outlive_the_whole_by_more_than_the_bound(self):
        for rho in (Q(0), Q(1, 2), Q(9, 10)):
            slack = 1 / (1 - rho)
            for p in POLS:
                part, whole = both(p, rho)
                self.assertLessEqual(part, whole + slack)

    def test_a_policy_as_good_for_the_part_as_serving_keeps_the_whole(self):
        for rho in (Q(0), Q(1, 2)):
            served = both(SERVE, rho)[0]
            for p in POLS:
                part, whole = both(p, rho)
                if part >= served:
                    self.assertGreaterEqual(whole, served - 1 / (1 - rho))

    def test_the_hypothesis_is_needed(self):
        part, whole = both(DEFECT, Q(1))
        self.assertEqual(whole, 3)
        self.assertGreater(part, 17)

    def test_the_bound_is_nearly_attained_without_independence(self):
        part, whole = both(DEFECT, Q(0))
        self.assertGreater(part, whole)
        self.assertLessEqual(part, whole + 1)
