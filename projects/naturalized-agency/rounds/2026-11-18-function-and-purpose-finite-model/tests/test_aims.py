from fractions import Fraction as Q
import unittest

from family import Lcg
from src.aims import (D, OUTCOMES, UNIFORM, aim, all_targets, constant, gain, hit,
                      interval_targets, policies)

A = [-1, 0, 1]
V = frozenset({0})
POLS = policies(A)
ANY = all_targets(OUTCOMES)
INT = interval_targets(OUTCOMES)


class Targets(unittest.TestCase):
    def test_unrestricted_targets_over_attribute(self):
        self.assertEqual(sum(aim(p, ANY, UNIFORM, A)[0] > 0 for p in POLS), 22)
        self.assertEqual(sum(aim(p, INT, UNIFORM, A)[0] > 0 for p in POLS), 13)

    def test_amplifier_and_canceller(self):
        amplifier = {d: d for d in D}
        self.assertEqual(aim(amplifier, ANY, UNIFORM, A)[0], Q(1, 3))
        self.assertEqual(aim(amplifier, INT, UNIFORM, A)[0], 0)
        canceller = {d: -d for d in D}
        self.assertEqual(aim(canceller, INT, UNIFORM, A), (Q(2, 3), [V]))

    def test_fixed_actions_have_no_aim(self):
        for a in A:
            self.assertEqual(aim(constant(a), ANY, UNIFORM, A)[0], 0)

    def test_serving_the_viable_set_bounds_the_aim_below(self):
        for p in POLS:
            self.assertGreaterEqual(aim(p, INT, UNIFORM, A)[0], gain(p, V, UNIFORM, A))

    def test_an_aim_need_not_serve(self):
        idle = hit(constant(0), V, UNIFORM)
        harmful = [p for p in POLS if aim(p, INT, UNIFORM, A)[0] > 0 and hit(p, V, UNIFORM) < idle]
        self.assertEqual(len(harmful), 4)


class TwoPriors(unittest.TestCase):
    def test_strength_moves_at_most_twice_the_distance_and_the_target_holds_past_four_times(self):
        g = Lcg(5)
        attained = False
        for _ in range(1500):
            w = [1 + g.below(20) for _ in D]
            w2 = [max(1, x + g.below(5) - 2) for x in w]
            p1 = {d: Q(x, sum(w)) for d, x in zip(D, w)}
            p2 = {d: Q(x, sum(w2)) for d, x in zip(D, w2)}
            delta = sum(abs(p1[d] - p2[d]) for d in D) / 2
            pol = POLS[g.below(len(POLS))]
            g1 = {T: gain(pol, T, p1, A) for T in INT}
            g2 = {T: gain(pol, T, p2, A) for T in INT}
            a1, a2 = max(g1.values()), max(g2.values())
            self.assertLessEqual(abs(a1 - a2), 2 * delta)
            attained = attained or (delta > 0 and abs(a1 - a2) == 2 * delta)
            top = [T for T in INT if g1[T] == a1]
            rest = [x for x in g1.values() if x != a1]
            if rest and a1 - max(rest) > 4 * delta:
                self.assertTrue(any(g2[T] == a2 for T in top))
        self.assertTrue(attained)
