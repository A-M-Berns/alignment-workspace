from fractions import Fraction as Q
from itertools import product
import unittest

from src.nested import ACTIONS, D, DEFECT, SERVE, inner_alive, lifetime, unserved

EPS, EPS_B = Q(1, 10), Q(1, 40)
POLS = [dict(zip(D, acts)) for acts in product(ACTIONS, repeat=3)]


def shirked(pol, h, rho):
    """Expected number of steps at which the part is alive and the whole is unserved."""
    return lifetime(pol, inner_alive, EPS, EPS_B, h, rho, count=unserved)


class ClosureBoundsShirking(unittest.TestCase):
    def test_every_policy(self):
        worst = Q(0)
        for h in (Q(1, 4), Q(1, 2)):
            for rho in (Q(0), Q(1, 2), Q(9, 10)):
                bound = 1 / (1 - h) + 1 / (1 - rho)
                for p in POLS:
                    x = shirked(p, h, rho)
                    self.assertLessEqual(x, bound)
                    worst = max(worst, x / bound)
        self.assertGreater(worst, Q(1, 2))

    def test_serving_shirks_nothing(self):
        self.assertEqual(shirked(SERVE, Q(1, 2), Q(1, 2)), 0)

    def test_without_the_parts_dependence_shirking_is_long(self):
        self.assertGreater(shirked(DEFECT, Q(1, 2), Q(1)), 16)

    def test_without_the_wholes_dependence_shirking_is_long(self):
        self.assertGreater(shirked(DEFECT, Q(1), Q(0)), 16)

    def test_a_long_lived_part_has_mostly_served(self):
        h, rho = Q(1, 2), Q(1, 2)
        bound = 1 / (1 - h) + 1 / (1 - rho)
        for p in POLS:
            life = lifetime(p, inner_alive, EPS, EPS_B, h, rho)
            served = life - shirked(p, h, rho)
            self.assertGreaterEqual(served, life - bound)
