"""The moral fixture, its population variant, and the legal fixture."""

from fractions import Fraction
import unittest

from src import fixtures

F = Fraction


class TestMoral(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        cls.out = fixtures.moral_fixture()

    def test_seed_is_humble(self):
        self.assertTrue(self.out["humble"])
        self.assertTrue(self.out["symmetry_generated_ok"])
        self.assertEqual(self.out["level_neutral_violations_without_impartiality"], {})
        # impartiality on the mirror pair plus completeness narrows a level: [1/2, 1]
        self.assertEqual(self.out["level_neutral_violations"],
                         {"r(a,b)": (F(1, 2), F(1)), "r(b,a)": (F(1, 2), F(1))})

    def test_declared_pairs_are_the_mirror_pairs(self):
        self.assertIn(("a", "b"), self.out["declared_pairs"])

    def test_dominance_forces_at_strength(self):
        iv = self.out["intervals"]
        self.assertEqual(iv["r(e,a)"], (F(4, 5), F(1)))
        self.assertEqual(iv["r(e,b)"], (F(4, 5), F(1)))
        self.assertEqual(iv["r(e,c)"], (F(4, 5), F(1)))

    def test_impartiality_forces_half_but_not_indifference(self):
        iv = self.out["intervals"]
        self.assertEqual(iv["r(a,b)"], (F(1, 2), F(1)))
        self.assertEqual(iv["r(b,a)"], (F(1, 2), F(1)))

    def test_additive_aggregation_not_forced(self):
        self.assertFalse(any(self.out["additive_forced"].values()))

    def test_interpersonal_comparability_is_open(self):
        self.assertIn("r(a,c)", self.out["open_axes"])
        self.assertIn("r(c,a)", self.out["open_axes"])

    def test_nothing_is_pinned(self):
        self.assertFalse(any(lo == hi for lo, hi in self.out["intervals"].values()))


class TestPopulation(unittest.TestCase):

    def test_structural_axioms_are_jointly_infeasible(self):
        out = fixtures.population_fixture()
        self.assertFalse(out["feasible"])
        cert = out["certificate"]
        self.assertIsNotNone(cert)
        labels = {c[2] for c in cert["support"] if c[0] == "str"}
        self.assertTrue(any("mere addition" in l for l in labels))
        self.assertTrue(any("P3" in l for l in labels))
        mis = {c[2] for c in out["mis"]}
        self.assertEqual(mis, {"P1 mere addition: r(B,A)=1 (>=)",
                               "P2 non-anti-egalitarian: r(C,B)=1 (>=)",
                               "P3': r(C,A)=0 (<=)", "trans(C,B,A)"})

    def test_humble_axioms_infeasible_above_two_thirds(self):
        self.assertFalse(fixtures.population_fixture(c=F(4, 5))["feasible"])
        self.assertTrue(fixtures.population_fixture(c=F(2, 3))["feasible"])


class TestLegal(unittest.TestCase):

    def test_validity_interval_and_amendment(self):
        out = fixtures.legal_fixture()
        before, after, defeated = out["before"], out["after_amendment"], out["right_defeated"]
        self.assertEqual(before["R"], (F(4, 5), F(1)))
        self.assertEqual(before["V"], (F(0), F(1, 5)))
        self.assertEqual(before["V2"], (F(0), F(1)))          # the open question
        self.assertEqual(before["G"], (F(0), F(0)))
        self.assertEqual(before["Sp"], (F(1), F(1)))
        self.assertEqual(after["V"], (F(1), F(1)))            # structural revision
        self.assertEqual(after["R"], (F(4, 5), F(1)))         # the right's strength untouched
        self.assertEqual(defeated["V"], (F(0), F(1)))         # docket defeat: widening, no pin
        self.assertEqual(defeated["R"], (F(0), F(1)))


if __name__ == "__main__":
    unittest.main()
