"""Exact mirrors of the Lean witnesses in `LICorrigibility.lean`."""

import unittest
from fractions import Fraction as Q

from src import compile as C
from src import mismatch as M


class LeanWitnesses(unittest.TestCase):

    def test_Witness_attained(self):
        # `indR true * D − indR false * D = D * (indR true * (1 − indR false))`
        D = Q(5, 3)
        rows = M.synthetic([(1, D, D, D, 1, 0, 0)])
        self.assertEqual(M.bypass(rows), D * M.mismatch_mass(rows))

    def test_Witness_marginal_refuted(self):
        D = Q(9)
        rows = M.synthetic([(Q(1, 2), D, D, 0, 1, 0, 0), (Q(1, 2), D, D, 0, 0, 1, 0)])
        self.assertEqual(M.bypass(rows), D / 2)
        self.assertEqual(M.marginal_difference(rows), Q(0))
        self.assertEqual(M.mismatch_mass(rows), Q(1, 2))

    def test_Witness_reverse_free(self):
        rows = M.synthetic([(1, 0, 0, Q(2, 7), 0, 1, 0)])
        self.assertLessEqual(M.bypass(rows), 0)
        self.assertEqual(M.mismatch_mass(rows), 0)

    def test_Witness_pair_rawOnly_and_both(self):
        # the pair: w_raw = 1, w_app = 1, w_act = 1/2, δ = 0, ρ = 1/2, λ = 1, D = dmax = 1
        L, D, DMAX = Q(1), Q(1), Q(1)
        raw_only = {"c_raw": True, "c_corr": False, "w_raw": Q(1), "w_app": Q(1),
                    "w_act": Q(1, 2), "delta": Q(0)}
        both = dict(raw_only, c_corr=True)
        self.assertEqual(C.constraint(raw_only, L, D, DMAX), Q(0))
        self.assertEqual(C.constraint(both, L, D, DMAX), Q(0))
        v = C.luvs(raw_only, L, D, DMAX)
        self.assertEqual((v["U_raw"], v["U_corr"], v["G_M"]), (Q(1), Q(0), Q(1)))
        v = C.luvs(both, L, D, DMAX)
        self.assertEqual((v["U_raw"], v["U_corr"], v["G_rho"], v["G_M"]), (Q(1), Q(1, 2), Q(1, 2), Q(0)))


if __name__ == "__main__":
    unittest.main()
