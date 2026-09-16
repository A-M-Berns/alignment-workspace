"""The five pressure tests, the defeat calculus against the grounded extension, and
stabilization."""

from fractions import Fraction
import unittest

from src import fixtures

F = Fraction


class TestPressure(unittest.TestCase):

    def test_1_dogmatic_item_leaves_a_permanent_trace(self):
        from src.seed import QUIET, Form, Seed, Settlement, SubItem, forced_interval
        frag, coh = fixtures.neg_fragment()
        S1 = Seed([SubItem(Form("premise", (0,), F(1)), 0, "dogmatic")], coh)
        S2 = Seed([], coh)
        self.assertFalse(S1.humble_items())
        self.assertEqual(forced_interval(S1, [], QUIET, Settlement(), 2, 0), (F(1), F(1)))
        self.assertEqual(forced_interval(S2, [], QUIET, Settlement(), 2, 0), (F(0), F(1)))

    def test_2_hysteresis(self):
        out = fixtures.hysteresis()
        a, b = out[("rho", "sigma")], out[("sigma", "rho")]
        self.assertEqual(a["interval"], (F(9, 10), F(95, 100)))
        self.assertEqual(b["interval"], (F(3, 10), F(1, 2)))
        self.assertNotEqual(a["interval"], b["interval"])
        self.assertEqual(out["canonical"]["interval"], (F(9, 10), F(95, 100)))

    def test_3_refinement_without_transport(self):
        out = fixtures.refinement()
        names = out["names"]
        p1 = names.index("p1")
        p = names.index("p")
        self.assertEqual(out["conservative"][p], (F(1, 2), F(1, 2)))
        self.assertEqual(out["conservative"][p1], (F(0), F(1, 2)))
        self.assertEqual(out["narrowing"][p1], (F(1, 2), F(1, 2)))
        self.assertEqual(out["narrowing"][p], (F(1, 2), F(1)))
        self.assertTrue(out["both_tau_equal"])

    def test_4_price_convergence_without_reason_convergence(self):
        out = fixtures.price_without_reason()
        self.assertEqual(out["I1"], (F(2, 3), F(1)))
        self.assertTrue(out["same_intervals"])
        self.assertTrue(out["disjoint_reasons"])

    def test_5_disguise(self):
        out = fixtures.disguise()
        self.assertEqual(out["level_caught"], {0: (F(1, 2), F(1, 2)), 1: (F(1, 2), F(1, 2))})
        self.assertEqual(out["relational_level"], {})
        self.assertTrue(out["relational_caught_by_declared_symmetry"])
        self.assertTrue(out["relational_passes_under_swap"])


class TestDefeat(unittest.TestCase):

    def test_grounded_versus_trace(self):
        out = fixtures.defeat_calculus()
        self.assertEqual(out["grounded"], {"W", "D2"})
        self.assertEqual(out["preferred"], [frozenset({"W", "D2"})])
        self.assertEqual(out["live_A"], {"W'", "D1'", "D2"})
        self.assertEqual(out["live_B"], {"W'", "D1", "D2"})
        self.assertEqual(out["live_C"], {"W", "D1", "D2"})


class TestStabilization(unittest.TestCase):

    def test_finite_class_is_eventually_constant(self):
        seq = fixtures.stabilization_finite()["sequence"]
        self.assertEqual(seq[0], (F(1, 2), F(1)))
        self.assertEqual(seq[1], (F(1, 2), F(1)))
        self.assertEqual(seq[2], (F(0), F(1)))
        self.assertEqual(seq[3], (F(3, 4), F(1)))
        self.assertEqual(seq[3], seq[4])

    def test_oscillation(self):
        out = fixtures.stabilization_oscillation()
        seq = out["sequence"]
        self.assertEqual(seq[::2], [(F(1, 2), F(1))] * 4)
        self.assertEqual(seq[1::2], [(F(0), F(1))] * 4)
        self.assertEqual(out["reopenings"], [F(1, 2)] * 4)

    def test_summable_reopenings_converge(self):
        out = fixtures.stabilization_summable()
        seq = out["sequence"]
        self.assertEqual(seq[0], (F(3, 4), F(1)))
        self.assertEqual(seq[1], (F(0), F(1)))
        self.assertEqual(seq[2], (F(5, 8), F(1)))
        self.assertEqual(seq[3], (F(1, 2), F(1)))
        self.assertEqual(out["drops"], [F(3, 4), F(1, 8), F(1, 16), F(1, 32), F(1, 64), F(1, 128)])
        self.assertEqual(out["drop_sum"], F(127, 128))
        self.assertEqual(seq[-1][0], F(1, 2))


if __name__ == "__main__":
    unittest.main()
