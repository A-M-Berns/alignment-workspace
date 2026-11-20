from fractions import Fraction as Q
import unittest

from src.nested import (D, DEFECT, NOTHING, SERVE, inner_alive, lifetime, shirk_tail,
                        survival, unserved)

EPS, EPS_B = Q(1, 10), Q(1, 40)
U, V = (1 - EPS) ** 2, (1 - EPS_B) ** 2
HALF_SERVE = {-1: 1, 0: 0, 1: 0}


class Tail(unittest.TestCase):
    def test_the_tail_bound(self):
        for h, rho in ((Q(1, 2), Q(1, 2)), (Q(1, 4), Q(9, 10)), (Q(1, 2), Q(0))):
            theta = max(h, rho)
            for pol in (DEFECT, NOTHING, HALF_SERVE):
                for m in range(2, 9):
                    self.assertLessEqual(shirk_tail(pol, EPS, EPS_B, h, rho, m), (m + 1) * theta ** (m - 2))

    def test_the_tail_sums_to_the_expectation(self):
        h, rho = Q(1, 2), Q(1, 2)
        expected = lifetime(DEFECT, inner_alive, EPS, EPS_B, h, rho, count=unserved)
        partial = sum(shirk_tail(DEFECT, EPS, EPS_B, h, rho, m) for m in range(1, 60))
        self.assertLess(partial, expected)
        self.assertLess(expected - partial, Q(1, 10 ** 6))

    def test_serving_never_shirks(self):
        self.assertEqual(shirk_tail(SERVE, EPS, EPS_B, Q(1, 2), Q(1, 2), 1), 0)


class LongRun(unittest.TestCase):
    def test_survivors_serve_exactly_when_u_exceeds_v_times_the_larger_independence(self):
        t = 400
        for h, rho in ((Q(1, 2), Q(4, 5)), (Q(1, 2), Q(9, 10)), (Q(9, 10), Q(0)), (Q(3, 4), Q(3, 4))):
            serve = survival(SERVE, inner_alive, EPS, EPS_B, h, rho, t)
            defect = survival(DEFECT, inner_alive, EPS, EPS_B, h, rho, t)
            self.assertEqual(serve > defect, U > V * max(h, rho))

    def test_longer_expected_life_and_better_long_run_survival_can_disagree(self):
        h, rho = Q(1, 2), Q(4, 5)
        self.assertGreater(lifetime(DEFECT, inner_alive, EPS, EPS_B, h, rho),
                           lifetime(SERVE, inner_alive, EPS, EPS_B, h, rho))
        self.assertLess(survival(DEFECT, inner_alive, EPS, EPS_B, h, rho, 400),
                        survival(SERVE, inner_alive, EPS, EPS_B, h, rho, 400))

    def test_serving_survives_at_rate_u(self):
        self.assertEqual(survival(SERVE, inner_alive, EPS, EPS_B, Q(1, 2), Q(1, 2), 30), U ** 30)
