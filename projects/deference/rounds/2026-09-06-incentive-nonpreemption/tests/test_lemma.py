import unittest
from fractions import Fraction as Q
from itertools import product

from src.lemma import (Frame, all_selectors, disagreement_mass, gain, grade_trust_level,
                       pair_gap, principal_regret, principal_regret_bound_cellwise,
                       selected_gap, sup_gain, valuation)


def frame(EX, W, J, sigma, p=None):
    cells = list(EX)
    p = p or {x: Q(1, len(cells)) for x in cells}
    return Frame(p, EX, W, J, sigma)


class Lemma(unittest.TestCase):
    def test_identity_holds_on_random_rational_frames(self):
        """gain = selected_gap + principal_regret, exhaustively over a small grid."""
        vals = [Q(0), Q(1, 2), Q(1), Q(-1)]
        menu = ("a", "b")
        for ex in product(vals, repeat=4):
            EX = {"x": {"a": ex[0], "b": ex[1]}, "y": {"a": ex[2], "b": ex[3]}}
            W = {"x": {"a": ex[3], "b": ex[0]}, "y": {"a": ex[1], "b": ex[2]}}
            for J in ({"x": "a", "y": "b"}, {"x": "b", "y": "b"}):
                for s in ({"x": "b", "y": "a"}, {"x": "a", "y": "a"}):
                    f = frame(EX, W, J, s, {"x": Q(1, 3), "y": Q(2, 3)})
                    self.assertEqual(gain(f), selected_gap(f) + principal_regret(f))
                    self.assertEqual(selected_gap(f),
                                     sum(pair_gap(f, j, m) for j in menu for m in menu))

    def test_grade_trust_is_the_pointwise_instance(self):
        EX = {"x": {"a": Q(9, 10), "b": Q(1, 5)}, "y": {"a": Q(1, 10), "b": Q(4, 5)}}
        W = {"x": {"a": Q(1), "b": Q(0)}, "y": {"a": Q(0), "b": Q(1)}}
        f = frame(EX, W, {"x": "a", "y": "b"}, {"x": "b", "y": "a"})
        eta = grade_trust_level(f)
        self.assertEqual(eta, Q(1, 5))
        self.assertLessEqual(selected_gap(f), 2 * eta * disagreement_mass(f))
        self.assertLessEqual(gain(f), 2 * eta * disagreement_mass(f) + principal_regret(f))

    def test_cellwise_argmax_composition(self):
        """(A): principal regret ≤ 2δ + 2ζ + η from cellwise calibration, any credence."""
        W = {"x": {"a": Q(1), "b": Q(0)}, "y": {"a": Q(0), "b": Q(1)}}
        w = {"x": {"a": Q(19, 20), "b": Q(1, 20)}, "y": {"a": Q(1, 20), "b": Q(19, 20)}}
        b = {"x": {"a": Q(9, 10), "b": Q(1, 10)}, "y": {"a": Q(1, 10), "b": Q(9, 10)}}
        EX = {"x": {"a": Q(1), "b": Q(1, 5)}, "y": {"a": Q(1, 5), "b": Q(1)}}
        for p in ({"x": Q(1, 2), "y": Q(1, 2)}, {"x": Q(1, 10), "y": Q(9, 10)}):
            f = frame(EX, W, {"x": "a", "y": "b"}, {"x": "b", "y": "a"}, p)
            d, z, e = principal_regret_bound_cellwise(f, b, w)
            self.assertEqual((d, z, e), (Q(1, 20), Q(1, 20), Q(0)))
            self.assertLessEqual(principal_regret(f), 2 * d + 2 * z + e)
            self.assertLessEqual(gain(f), selected_gap(f) + 2 * d + 2 * z + e)

    def test_sup_over_selectors_is_algebra_once_st_is_per_selector(self):
        EX = {"x": {"a": Q(1), "b": Q(1, 2)}, "y": {"a": Q(1, 2), "b": Q(1)}}
        W = {"x": {"a": Q(1), "b": Q(0)}, "y": {"a": Q(0), "b": Q(1)}}
        J = {"x": "a", "y": "b"}
        f0 = frame(EX, W, J, J)
        sels = list(all_selectors(f0))
        eps = max(selected_gap(frame(EX, W, J, s)) for s in sels)
        r = max(principal_regret(frame(EX, W, J, s)) for s in sels)
        self.assertLessEqual(sup_gain(f0, sels), eps + r)
        self.assertEqual(sup_gain(f0, sels), Q(0))   # J is EX-optimal here too


if __name__ == "__main__":
    unittest.main()
