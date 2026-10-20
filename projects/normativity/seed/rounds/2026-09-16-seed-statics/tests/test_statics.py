"""Statics: forced region, intervals, monotonicity, defeat widening, certificates, and
the cross-check of the simplex against the elimination the Lean file proves correct."""

from fractions import Fraction
import unittest

from src import fixtures, fm, lp
from src.seed import (QUIET, DocketState, Form, Fragment, Seed, Settlement, StrItem, SubItem,
                      check_compiled, forced_bundle, forced_interval, in_region)

F = Fraction


class TestStatics(unittest.TestCase):

    def test_check_compiled_decides_membership(self):
        frag, coh = fixtures.neg_fragment()
        S = Seed([SubItem(Form("premise", (0,), F(1, 2)), 0)], coh)
        B = forced_bundle(S, [], QUIET, Settlement(), 2)
        self.assertTrue(check_compiled(B, [F(1, 2), F(1, 2)]))
        self.assertTrue(check_compiled(B, [F(1), F(0)]))
        self.assertFalse(check_compiled(B, [F(1, 4), F(3, 4)]))    # violates P(phi) >= 1/2
        self.assertFalse(check_compiled(B, [F(1, 2), F(1, 4)]))    # violates coherence

    def test_settlement_specializes_rows(self):
        frag = Fragment(["p", "q"])
        r = frag.row({"p": 1, "q": 2}, 3)
        Fs = Settlement({1: True})
        s = Fs.specialize(r)
        self.assertEqual(list(s.a), [F(1), F(0)])
        self.assertEqual(s.b, F(1))
        x = [F(1, 2), F(1)]
        self.assertTrue(Fs.pinned(x))
        self.assertEqual(r.sat(x), s.sat(x))

    def test_monotonicity_under_settlement(self):
        out = fixtures.settlement_monotone()
        self.assertTrue(out["chain_ok"])
        self.assertTrue(out["nested"])
        self.assertEqual(out["intervals"][0][0], (F(0), F(1)))
        self.assertEqual(out["intervals"][1][0], (F(0), F(0)))     # p <= q <= r = 0

    def test_defeat_widens(self):
        out = fixtures.defeat_widening()
        self.assertEqual(out["before"], (F(1, 2), F(1)))
        self.assertEqual(out["after"], (F(0), F(1)))

    def test_farkas_and_bound_certificates(self):
        frag = Fragment(["p"])
        rows = [frag.row({"p": -1}, -F(3, 4)).pair(), frag.row({"p": 1}, F(1, 2)).pair()]
        self.assertFalse(lp.feasible(rows, 1))
        lam = lp.farkas_certificate(rows, 1)
        self.assertIsNotNone(lam)
        self.assertTrue(lp.verify_farkas(rows + lp.cube_rows(1), 1, lam))
        rows2 = [frag.row({"p": -1}, -F(3, 4)).pair()]
        self.assertEqual(lp.interval(rows2, 1, 0), (F(3, 4), F(1)))
        cert = lp.bound_certificate(rows2, 1, 0, -1, -F(3, 4))
        self.assertIsNotNone(cert)
        self.assertEqual(sum(l * F(r[1]) for l, r in zip(cert, rows2 + lp.cube_rows(1))), -F(3, 4))

    def test_simplex_agrees_with_elimination(self):
        frag = Fragment(["p", "q", "r"])
        rows = [frag.row({"p": 1, "q": -1}, 0).pair(), frag.row({"q": 1, "r": -1}, 0).pair(),
                frag.row({"r": 1}, F(2, 3)).pair(), frag.row({"p": -1}, -F(1, 5)).pair()]
        for phi in range(3):
            self.assertEqual(lp.interval(rows, 3, phi), fm.fm_interval(rows, 3, phi))
        self.assertEqual(lp.interval(rows, 3, 0), (F(1, 5), F(2, 3)))
        infeasible = rows + [frag.row({"p": -1}, -F(3, 4)).pair()]
        self.assertIsNone(lp.interval(infeasible, 3, 0))
        self.assertIsNone(fm.fm_interval(infeasible, 3, 0))

    def test_sandwich_pins_under_item_humility(self):
        out = fixtures.sandwich()
        self.assertTrue(out["humble"])
        self.assertEqual(out["I1"], (F(1, 2), F(1, 2)))
        self.assertEqual(out["I2"], (F(0), F(1)))
        self.assertEqual(out["fm_I1"], out["I1"])

    def test_strict_humility_refutes_instead_of_pinning(self):
        out = fixtures.strict_humility()
        self.assertEqual(out["closed_layer"], (F(0), F(1, 2)))
        self.assertEqual(out["closed_item"], (F(1, 2), F(1, 2)))
        self.assertEqual(out["closed_item_fm"], (F(1, 2), F(1, 2)))
        self.assertTrue(out["closed_item_feasible"])
        self.assertFalse(out["strict_item_feasible"])

    def test_c1_measure_form_refuted(self):
        out = fixtures.c1_measure_form()
        self.assertTrue(out["hull_holds"])
        self.assertFalse(out["measure_holds"])
        self.assertEqual(out["gap"], F(9, 10))
        self.assertEqual(out["measure"], F(1, 5))


if __name__ == "__main__":
    unittest.main()
