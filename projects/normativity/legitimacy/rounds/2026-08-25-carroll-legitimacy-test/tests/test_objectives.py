"""Gate B: Table 4 recovered, and every cell that is not recovered characterised."""
from __future__ import annotations

import unittest

import carroll_cases as cc
import drmdp
import objectives as ob
import table4


class TestTable4(unittest.TestCase):

    def test_every_cell_is_recovered_under_a_stated_reading(self):
        """The two exceptions are exactly Table 4's over-quantified cells."""
        for case, name, row in table4.mismatches():
            self.assertTrue(row.get("quantified"),
                            f"{case}/{name} is not a quantified cell")
            self.assertFalse(row.get("stated_theta0"),
                             f"{case}/{name} is the example's own theta_0")

    def test_the_two_exceptions_are_the_expected_ones(self):
        self.assertEqual(
            sorted((c, n) for c, n, _ in table4.mismatches()),
            [("Clickbait", "InitialReward[theta_0=th_disillusioned]"),
             ("WritersCurse", "InitialReward[theta_0=th_unhappy]")])

    def test_one_cell_depends_on_definition_5s_index_range(self):
        """`xi^theta = (theta_0..theta_{H-1})` loses the last step's influence."""
        self.assertEqual(
            [(c, n) for c, n, _ in table4.reading_sensitive()],
            [("Clickbait", "ConstrainedRTReward")])

    def test_vacuous_cells_are_declared(self):
        """Cells every policy is optimal for establish nothing, and are listed."""
        self.assertEqual(
            sorted(table4.vacuous()),
            sorted([("WritersCurse", "MyopicReward"),
                    ("Dehydration", "MyopicReward"),
                    ("Dehydration", "InitialReward[theta_0=3]"),
                    ("Dehydration", "InitialReward[theta_0=4]")]))

    def test_the_recovered_cells_outnumber_the_exceptions(self):
        rows = table4.rows()
        good = [r for _, r in rows if table4.recovered(r)]
        self.assertEqual((len(good), len(rows)), (50, 52))


class TestWritersCurseReading(unittest.TestCase):
    """The reading of Figure 2 is forced by Table 4, not chosen."""

    def test_the_absorbing_reading_loses_the_final_reward_cell(self):
        m = cc.writers_curse(poetry_absorbing=True)
        H = cc.HORIZON["WritersCurse"]
        paper = ob.materialise(
            m, H, table4.POLICIES["WritersCurse"]["FinalReward"][0])
        best = ob.argmax(m, H, ob.u_final, cc.NOOP)
        self.assertFalse(any(ob.key(paper) == ob.key(p) for p in best))

    def test_the_chosen_reading_keeps_it_and_keeps_it_uniquely(self):
        m = cc.writers_curse()
        H = cc.HORIZON["WritersCurse"]
        paper = ob.materialise(
            m, H, table4.POLICIES["WritersCurse"]["FinalReward"][0])
        best = ob.argmax(m, H, ob.u_final, cc.NOOP)
        self.assertEqual(len(best), 4)   # equal off the reachable-but-unvisited
        self.assertTrue(any(ob.key(paper) == ob.key(p) for p in best))


class TestInfluence(unittest.TestCase):
    """Definitions 5-7, on the examples the source states them about."""

    def test_real_time_influences_in_the_conspiracy_case(self):
        m, H = cc.conspiracy_influence(), cc.HORIZON["ConspiracyInfluence"]
        best = ob.argmax(m, H, ob.u_real_time, cc.NOOP)
        self.assertTrue(ob.influence_incentive(m, H, cc.NOOP, best))

    def test_constrained_real_time_does_not(self):
        m, H = cc.conspiracy_influence(), cc.HORIZON["ConspiracyInfluence"]
        best = ob.argmax(m, H, ob.u_real_time, cc.NOOP,
                         over=ob.constrained_policies(m, H, cc.NOOP))
        self.assertFalse(any(ob.influences(m, p, H, cc.NOOP) for p in best))

    def test_the_horizon_matters_where_the_source_says_it_does(self):
        """Figure 1 influences under real-time reward for horizons above two."""
        m = cc.conspiracy_influence()
        got = {}
        for H in range(1, 6):
            best = ob.argmax(m, H, ob.u_real_time, cc.NOOP)
            got[H] = ob.influence_incentive(m, H, cc.NOOP, best)
        self.assertEqual(got, {1: False, 2: False, 3: True, 4: True, 5: True})

    def test_natural_shift_is_grounded_in_the_inaction_policy(self):
        m, H = cc.clickbait(), cc.HORIZON["Clickbait"]
        marg = ob.noop_marginals(m, H, cc.NEWS)
        self.assertTrue(all(mt == ((cc.TH_NORMAL, 1),) for mt in marg))


class TestExactness(unittest.TestCase):

    def test_every_value_is_a_rational(self):
        from fractions import Fraction
        for name, build in cc.CASES.items():
            m, H = build(), cc.HORIZON[name]
            a_noop = cc.NOOP_ACTION[name]
            for pol in drmdp.policies(m, H)[:8]:
                for U in (ob.u_real_time, ob.u_final, ob.u_initial,
                          ob.u_natural_shifts):
                    self.assertIsInstance(U(m, pol, H, a_noop=a_noop), Fraction)

    def test_the_policy_cap_refuses_rather_than_samples(self):
        m = cc.dehydration()
        with self.assertRaises(ValueError):
            drmdp.policies(m, cc.HORIZON["Dehydration"], cap=3)


if __name__ == "__main__":
    unittest.main()
