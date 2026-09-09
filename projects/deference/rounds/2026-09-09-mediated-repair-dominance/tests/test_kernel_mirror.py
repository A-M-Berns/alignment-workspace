"""Numerical mirrors of the Lean kernel's statements, on synthetic rows and on a small
exhaustive grid of the theorem's hypotheses."""

import itertools
import unittest
from fractions import Fraction as Q

from src.analysis import premium_def, bound, kappa, rho, void


def rows_of(table):
    return [{"p": p, "w_raw": wr, "w_app": wa, "w_act": wc, "c_raw": cr, "c_lift": cl, "z": i}
            for i, (p, wr, wa, wc, cr, cl) in enumerate(table)]


class KernelMirror(unittest.TestCase):

    def test_totalVoid(self):
        rows = rows_of([(Q(1), Q(0), Q(0), Q(0), False, True)])
        D = Q(1)
        self.assertEqual(kappa(rows), 0)
        self.assertEqual(rho(rows), 0)
        self.assertEqual(void(rows, "c_raw"), 1)
        self.assertEqual(void(rows, "c_lift"), 0)
        self.assertEqual(premium_def(rows, lambda r: Q(1), lambda r: Q(0)), 1)
        self.assertEqual(bound(rows, D), 1)

    def test_tightKappa(self):
        rows = rows_of([(Q(3, 4), Q(4), Q(4), Q(4), True, True),
                        (Q(1, 4), Q(4), Q(0), Q(0), True, True)])
        self.assertEqual(kappa(rows), 1)
        self.assertEqual(premium_def(rows, lambda r: 0, lambda r: 0), 1)
        self.assertEqual(bound(rows, Q(4)), 1)

    def test_bypass_premium_le_on_a_grid(self):
        vals = [Q(0), Q(1, 2), Q(1)]
        D = Q(1)
        for wr, wa, wc, cr, cl in itertools.product(vals, vals, vals, (False, True),
                                                    (False, True)):
            rows = rows_of([(Q(1), wr, wa, wc, cr, cl)])
            for br in vals:
                for bl in vals:
                    if cr and br != wr:
                        continue
                    if cl and bl != wc:
                        continue
                    phi = premium_def(rows, lambda r: br, lambda r: bl)
                    self.assertLessEqual(phi, bound(rows, D))


if __name__ == "__main__":
    unittest.main()
