"""The moral and legal fixtures."""

from fractions import Fraction
import unittest

from src import fixtures as X

F = Fraction


class TestMoral(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        cls.out = X.moral_two()

    def test_chain_narrows_hull_and_keeps_discord(self):
        s0, s1, s2 = self.out["steps"]
        self.assertEqual(s0["profile"], (F(47, 60), F(3, 5), F(1, 6)))
        self.assertEqual(s1["profile"], (F(47, 60), F(3, 5), F(1, 6)))
        self.assertEqual(s2["profile"], (F(7, 12), F(3, 10), F(1, 6)))
        for s in (s0, s1, s2):
            self.assertEqual(s["delta"], ["r(a,c)", "r(b,c)"])
            self.assertEqual(s["refuted"], [])
        self.assertEqual(s0["hulls"]["r(e,a)"], (F(0), F(1)))
        self.assertEqual(s2["hulls"]["r(e,a)"], (F(4, 5), F(1)))
        self.assertEqual(s2["hulls"]["r(a,b)"], (F(1, 2), F(1)))

    def test_reference_profile_of_empty_seeds(self):
        self.assertEqual(self.out["reference_profile"], (F(43, 60), F(43, 60), 0))

    def test_aggregation_disagreement_is_discord_with_certificate(self):
        cert = self.out["certificate"]
        self.assertEqual(cert["gap"], F(3, 5))
        self.assertEqual({c[2] for c in cert["minimal_infeasible_subset"]},
                         {"prioritarian: not r(a,c)", "sum: r(a,c)"})

    def test_sharing_the_conflicting_item_refutes(self):
        self.assertEqual(self.out["share_conflicting"]["refuted"], ["R1"])

    def test_sharing_a_neutral_warrant_narrows_the_hull(self):
        n = self.out["share_neutral"]
        self.assertEqual(n["profile"], (F(11, 20), F(17, 60), F(1, 6)))
        self.assertEqual(n["hull_rab"], (F(7, 10), F(1)))
        self.assertEqual(n["delta"], ["r(a,c)", "r(b,c)"])


class TestPopulation(unittest.TestCase):

    def test_private_learning_creates_discord(self):
        out = X.population_private()
        self.assertEqual(out["before"], (F(1), F(11, 15), 0))
        self.assertEqual(out["after"], (F(1), F(4, 15), F(1, 3)))
        self.assertEqual(out["delta_after"], ["r(A,C)", "r(C,A)"])
        self.assertEqual(out["certificate"]["gap"], F(2, 5))
        self.assertEqual(out["shared_refuted"], ["R2"])


class TestLegal(unittest.TestCase):

    def test_two_courts(self):
        steps = X.legal_two()["steps"]
        self.assertEqual(steps[0]["profile"], (F(1), F(17, 20), 0))
        self.assertEqual(steps[1]["profile"], (F(13, 20), F(1, 2), F(1, 2)))
        self.assertEqual(steps[2]["profile"], steps[1]["profile"])
        self.assertEqual(steps[2]["court2_pick"], F(7, 10))
        self.assertEqual(steps[2]["I"]["court1"]["V"], (F(0), F(1, 10)))
        self.assertEqual(steps[2]["I"]["court2"]["V"], (F(3, 10), F(3, 10)))
        self.assertEqual(steps[2]["hulls"]["V2"], (F(0), F(1)))
        self.assertEqual({c[2] for c in steps[2]["certificate"]["minimal_infeasible_subset"]},
                         {"locked right 9/10", "presumption P(V)>=3/10"})


if __name__ == "__main__":
    unittest.main()
