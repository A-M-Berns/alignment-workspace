"""The rule, the run, the two exhibits — exact rationals, recomputed and compared exactly."""
from __future__ import annotations

import unittest
from fractions import Fraction as F

from rebuttal import (C, COHERENCE, GROUNDS, KEPT, N0, N1, NE, REBUTTED, RETIRED, RHO, VACUOUS, X,
                      XA, XAY, Y, Z, Occurrence, defeated_at, fm_eliminate, constraints, hull_mass,
                      interval, live, odds, port_only_live, reopening, row_of, run_table,
                      settle_outcome, settlement_at, survivors)
from exhibit import cushion_exhibit, nothing_to_buy


class TheRule(unittest.TestCase):

    def test_three_outcomes(self):
        s = (True, None, False, False, None)        # X true, Y refuted, closure
        self.assertEqual(settle_outcome(s, ("premise", X, C["P"])), KEPT)
        self.assertEqual(settle_outcome(s, ("applicability", X, XA, C["A"])), KEPT)
        self.assertEqual(settle_outcome(s, ("strength", XA, XAY, C["S"])), REBUTTED)
        s2 = (False, False, False, None, None)      # X refuted
        self.assertEqual(settle_outcome(s2, ("premise", X, C["P"])), RETIRED)
        self.assertEqual(settle_outcome(s2, ("applicability", X, XA, C["A"])), VACUOUS)
        self.assertEqual(settle_outcome(s2, ("strength", XA, XAY, C["S"])), VACUOUS)

    def test_vacuity_before_rebuttal(self):
        s = (None, False, False, None, None)        # antecedent and consequent both false
        self.assertEqual(settle_outcome(s, ("strength", XA, XAY, C["S"])), VACUOUS)

    def test_no_discount(self):
        # the kept row is the form's own row, strength untouched
        s = (True, None, None, None, None)
        self.assertEqual(row_of(("applicability", X, XA, C["A"])), row_of(("applicability", X, XA, F(3, 4))))

    def test_contraposing_shape(self):
        # the strength row with XAY pinned 0 forces XA ≤ 0: the row the rule removes
        a, b = row_of(("strength", XA, XAY, C["S"]))
        x = [F(1), F(1, 10), F(0), F(0), F(1)]     # XA positive, XAY = 0
        self.assertGreater(sum(ai * xi for ai, xi in zip(a, x)), b)

    def test_retirement_reaches_the_warrant_under_closure(self):
        s2 = (False, False, False, None, None)     # X refuted, with its closure X∧A, X∧A∧Y false
        ids = [o.id for o in survivors(GROUNDS, set(), s2)]
        self.assertEqual(ids, [4])                 # the premise retired, its chain gone, Z stays

    def test_retirement_needs_closure(self):
        # without the closure pins the applicability form is vacuous (X false) but the strength
        # form, whose antecedent X∧A is unpinned and which cites the vacuous — not retired —
        # applicability, survives: the one-step retirement rule relies on closed settlements
        s2 = (False, None, None, None, None)
        ids = [o.id for o in survivors(GROUNDS, set(), s2)]
        self.assertEqual(ids, [3, 4])


class TheRun(unittest.TestCase):

    def setUp(self):
        self.table = run_table()

    def test_survivors_by_phase(self):
        got = {r["date"]: r["survivors"] for r in self.table}
        self.assertEqual(got[0], [1, 2, 3, 4])
        self.assertEqual(got[N1], [1, 2, 3, 4])
        self.assertEqual(got[N0], [1, 3, 4])
        self.assertEqual(got[NE], [1, 4])

    def test_intervals_by_elimination(self):
        got = {r["date"]: r for r in self.table}
        self.assertEqual(got[0]["I_XAY"], (F(2, 5), F(1)))
        self.assertEqual(got[0]["I_XA"], (F(3, 5), F(1)))
        self.assertEqual(got[N1]["I_XAY"], (F(1, 2), F(1)))
        self.assertEqual(got[N1]["I_XA"], (F(3, 4), F(1)))
        self.assertEqual(got[N0]["I_XAY"], (F(0), F(1)))
        self.assertEqual(got[N0]["I_XA"], (F(0), F(1)))
        self.assertEqual(got[NE]["I_XAY"], (F(0), F(0)))
        self.assertEqual(got[NE]["I_XA"], (F(0), F(1)))
        for r in self.table:
            self.assertEqual(r["I_Z"], (F(1, 2), F(1)))

    def test_settlement_nests(self):
        a, b = self.table[N1 - 1], self.table[N1]
        for k in ("I_XA", "I_XAY", "I_Z"):
            self.assertGreaterEqual(b[k][0], a[k][0])
            self.assertLessEqual(b[k][1], a[k][1])
        self.assertEqual(a["survivors"], b["survivors"])

    def test_undercut_widens(self):
        self.assertEqual(self.table[N0 - 1]["I_XA"], (F(3, 4), F(1)))
        self.assertEqual(self.table[N0]["I_XA"], (F(0), F(1)))

    def test_rebuttal_is_the_one_reopening(self):
        self.assertEqual([r["date"] for r in self.table if r["reopening"]], [NE])
        self.assertEqual(self.table[NE]["reopening"], [3])

    def test_reopening_widens_XA_by_zero(self):
        # the kept rows at the pre-step settlement force [0,1] on XA; new interval [0,1]: widening 0
        kept = survivors(GROUNDS, defeated_at(NE), settlement_at(NE))
        pre = fm_eliminate(constraints(kept, COHERENCE, settlement_at(NE - 1)), XA)
        self.assertEqual(pre, (F(0), F(1)))
        self.assertEqual(self.table[NE]["I_XA"], pre)
        self.assertEqual(self.table[NE - 1]["I_XA"], (F(0), F(1)))

    def test_old_rule_pins_XA(self):
        old = interval(GROUNDS, defeated_at(NE), settlement_at(NE), COHERENCE, XA, rule=port_only_live)
        self.assertEqual(old, (F(0), F(0)))

    def test_no_row_on_XA_after_rebuttal(self):
        for r in self.table:
            self.assertEqual(r["holds_XA"], r["date"] < NE)

    def test_hull_mass_sequence(self):
        w = {XA: F(1, 3), XAY: F(1, 3), Z: F(1, 3)}
        hm = [hull_mass({XA: r["I_XA"], XAY: r["I_XAY"], Z: r["I_Z"]}, w) for r in self.table]
        self.assertEqual(hm[0], F(1, 2))
        self.assertEqual(hm[N1], F(5, 12))
        self.assertEqual(hm[N0], F(5, 6))
        self.assertEqual(hm[NE], F(1, 2))
        self.assertEqual(hm[NE:], [F(1, 2)] * len(hm[NE:]))   # eventually constant

    def test_slack_world_after_rebuttal(self):
        lw = live(NE)
        surv = survivors(GROUNDS, defeated_at(NE), settlement_at(NE))
        from rebuttal import gap
        self.assertTrue(any(all(gap(row_of(o.form), w) > 0 for o in surv) for w in lw.values()))

    def test_odds(self):
        self.assertEqual(RHO, 4)


class TheExhibits(unittest.TestCase):

    def test_nothing_to_buy(self):
        led = nothing_to_buy(F(10), 200)
        self.assertEqual(led["position"], 0)
        self.assertEqual(led["enforcer_book"], 0)

    def test_same_three_rho_refuted(self):
        ex = cushion_exhibit()
        self.assertEqual(ex["loss"], 24)
        self.assertEqual(3 * RHO, 12)
        self.assertGreater(ex["loss"], 3 * RHO)
        self.assertLessEqual(ex["loss"], ex["sharp_bound"])              # 27
        self.assertLessEqual(ex["sharp_bound"], 3 * RHO * (2 + RHO))      # 72, the proved bound
        self.assertLess(ex["enforcer_at_A_true"], 3)                     # within the maker's capital


if __name__ == "__main__":
    unittest.main()
