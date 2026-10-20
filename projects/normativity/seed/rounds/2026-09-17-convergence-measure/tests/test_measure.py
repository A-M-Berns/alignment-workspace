"""The profile, its inequalities, the five gameability attacks, and dynamics on the
small fixtures."""

from fractions import Fraction
import unittest

from src import fixtures as X
from src.profile import profile

F = Fraction


class TestMeasure(unittest.TestCase):

    def test_touching_refutes_disc_zero_implies_ovl_pos(self):
        out = X.touching()
        self.assertEqual(out["discord"], 0)
        self.assertEqual(out["overlap"], F(0))
        self.assertEqual(out["hull"], F(1))

    def test_basic_inequalities_on_fixtures(self):
        for out in (X.touching(), X.hiding()["wide_vs_narrow"], X.hiding()["narrow_vs_narrow"]):
            self.assertLessEqual(out["overlap"], out["hull"])
            self.assertLessEqual(out["hull"], F(1))
            self.assertGreaterEqual(out["discord"], 0)


class TestGameability(unittest.TestCase):

    def test_1_dilution(self):
        out = X.dilution()
        self.assertEqual(out["naive_small"], F(1))
        self.assertEqual(out["naive_diluted"], F(1, 4))
        self.assertEqual(out["blocked_small"], F(1))
        self.assertEqual(out["blocked_diluted"], F(1))

    def test_2_splitting(self):
        out = X.splitting()
        self.assertEqual(out["before"], F(1))
        self.assertEqual(out["declared_after"], F(1))
        self.assertEqual(out["declared_discord"], F(1))
        self.assertEqual(out["refined_discord"], 0)          # discord hidden by splitting
        self.assertEqual(out["refined_hulls"], {1: (F(0), F(1)), 2: (F(0), F(1))})

    def test_4_hiding(self):
        out = X.hiding()
        wide, narrow = out["wide_vs_narrow"], out["narrow_vs_narrow"]
        self.assertEqual((wide["hull"], wide["overlap"], wide["discord"]), (F(1), F(1, 5), 0))
        self.assertEqual((narrow["hull"], narrow["overlap"], narrow["discord"]), (F(1), F(0), F(1)))

    def test_5_weight_capture(self):
        out = X.weight_capture()
        self.assertEqual(out[F(1, 1000)], F(1, 1000))
        self.assertEqual(out["uniform"], F(1, 2))
        self.assertTrue(all(v > 0 for v in out.values()))


class TestDynamics(unittest.TestCase):

    def test_private_learning_creates_discord_sharing_refutes_defeat_dissolves(self):
        out = X.private_learning()
        b, p, s, dfd = out["before"], out["private"], out["shared"], out["defeated"]
        self.assertEqual((b["hull"], b["overlap"], b["discord"]), (F(1), F(1, 10), 0))
        self.assertEqual((p["hull"], p["overlap"], p["discord"]), (F(1), F(0), F(1)))
        cert = out["certificate"]
        self.assertEqual(cert["gap"], F(1, 5))
        self.assertEqual({c[2] for c in cert["minimal_infeasible_subset"]},
                         {"P(phi)<=2/5", "w: P(phi)>=3/5"})
        self.assertEqual(s["refuted"], ["R1"])
        self.assertEqual((dfd["hull"], dfd["discord"]), (F(1), 0))

    def test_oscillation_two(self):
        seq = X.oscillation_two()["hull_sequence"]
        self.assertEqual(seq, [F(7, 10), F(1)] * 4)

    def test_persistent_discord_certified_along_chain(self):
        steps = X.persistent_discord()["steps"]
        self.assertEqual(steps[0]["profile"], (F(1), F(1, 2), F(1, 2)))
        self.assertEqual(steps[1]["profile"], (F(1, 2), F(0), F(1, 2)))
        for s in steps:
            self.assertEqual(s["delta"], [0])
            self.assertEqual(s["gap"], F(2, 5))
            self.assertEqual({c[2] for c in s["mis"]}, {"P(phi)>=4/5", "P(phi)<=2/5"})

    def test_lock(self):
        out = X.lock()
        for step in out["chain"]:
            self.assertEqual(step["R2_pick"], F(4, 5))
            self.assertEqual(step["profile"], (F(3, 20), F(1, 20), 0))
            self.assertEqual(step["I"]["R1"][1], (F(9, 10), F(19, 20)))
        opp = out["opposed"]
        self.assertEqual(opp["profile"], (F(2, 5), F(0), F(1)))
        self.assertEqual({c[2] for c in opp["certificate"]["minimal_infeasible_subset"]},
                         {"locked right 9/10", "presumption 3/10"})

    def test_consensus_without_reasons_and_its_fragility(self):
        out = X.consensus()
        a, f = out["agree"], out["after_one_sided_defeater"]
        self.assertTrue(out["disjoint_dockets"])
        self.assertEqual((a["hull"], a["overlap"], a["discord"]), (F(1, 3), F(1, 3), 0))
        self.assertEqual((f["hull"], f["overlap"], f["discord"]), (F(1), F(1, 3), 0))


class TestSolver(unittest.TestCase):

    def test_warm_start_agrees_with_seed_round_solver(self):
        from src.profile import multi_interval, S, lp
        out = X.private_learning()
        frag = S.Fragment(["phi"])
        for c in (F(3, 5), F(3, 10)):
            R = X.Reasoner("R", S.Seed([X.prem(0, c, 0)], []), [], X.QUIET)
            rows = [r.pair() for _, r in R.region_rows(S.Settlement(), 1)]
            self.assertEqual(multi_interval(rows, 1, [0])[0], lp.interval(rows, 1, 0))
        # a relational case
        frag2 = S.Fragment(["x", "y"])
        R = X.Reasoner("R", S.Seed([S.SubItem(S.Form("applicability", (0, 1), F(9, 10)), 0),
                                    X.prem(0, F(4, 5), 2)], []), [], X.QUIET)
        rows = [r.pair() for _, r in R.region_rows(S.Settlement(), 2)]
        mi = multi_interval(rows, 2, [0, 1])
        self.assertEqual(mi[0], lp.interval(rows, 2, 0))
        self.assertEqual(mi[1], lp.interval(rows, 2, 1))
        self.assertEqual(mi[1], (F(18, 25), F(1)))


class TestMany(unittest.TestCase):

    def test_hidden_discord(self):
        out = X.hidden_discord()
        two, three = out["two"], out["three"]
        self.assertEqual(two["profile"], (F(1), F(1, 4), 0))
        self.assertFalse(two["merged_feasible"])
        self.assertEqual({c[1][2] for c in two["certificate"]["minimal_infeasible_subset"]},
                         {"y>=0.9x", "x>=4/5", "y<=3/10"})
        self.assertEqual(three["profile"], (F(1), F(2, 5), 0))
        self.assertTrue(all(three["pairwise_feasible"].values()))
        self.assertFalse(three["merged_feasible"])
        self.assertEqual(three["graph"], [])
        self.assertEqual({c[0] for c in three["certificate"]["minimal_infeasible_subset"]},
                         {"A", "B", "C"})


if __name__ == "__main__":
    unittest.main()
