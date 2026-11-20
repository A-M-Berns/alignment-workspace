from fractions import Fraction as Q
import unittest

from src.acquired import (BOOST, BUILD, POLICIES, SERVE, inner_alive, lifetime,
                          whole_alive)

EPS, EPS_B, H = Q(1, 10), Q(1, 40), Q(1, 2)
SERVING = {False: SERVE, True: SERVE}
BUILD_THEN_BOOST = {False: BUILD, True: BOOST}


def part(pol, delta):
    return lifetime(pol, inner_alive, EPS, EPS_B, H, delta)


def whole(pol, delta, *start):
    return lifetime(pol, whole_alive, EPS, EPS_B, H, delta, *start)


class BuiltIndependence(unittest.TestCase):
    def test_a_store_that_lapses_fast_leaves_serving_unbeaten(self):
        best = max(part(p, Q(1, 4)) for p in POLICIES)
        self.assertEqual(best, part(SERVING, Q(1, 4)))
        self.assertEqual(best, Q(100, 19))

    def test_a_durable_store_makes_building_then_boosting_strictly_best(self):
        d = Q(1, 10)
        top = part(BUILD_THEN_BOOST, d)
        self.assertEqual(top, Q(5500218221251, 817862668900))
        for p in POLICIES:
            if p != BUILD_THEN_BOOST:
                self.assertLess(part(p, d), top)
        self.assertEqual(part(BUILD_THEN_BOOST, Q(0)), Q(4771, 316))

    def test_the_whole_then_fares_as_with_the_part_absent(self):
        d = Q(1, 10)
        self.assertEqual(whole(BUILD_THEN_BOOST, d), 3)
        self.assertEqual(whole(SERVING, d, frozenset(["Wb", "Service"])), 3)
        self.assertEqual(whole(SERVING, d), Q(157, 19))

    def test_where_the_policies_cross(self):
        self.assertGreater(part(BUILD_THEN_BOOST, Q(1, 6)), part(SERVING, Q(1, 6)))
        self.assertLess(part(BUILD_THEN_BOOST, Q(2, 11)), part(SERVING, Q(2, 11)))
