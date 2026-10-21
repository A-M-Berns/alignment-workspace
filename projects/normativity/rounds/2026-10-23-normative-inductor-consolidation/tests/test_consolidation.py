"""The compile outcome, the two scenarios, the same question before and after — exact rationals."""
from __future__ import annotations

import unittest
from fractions import Fraction as F

from consolidation import (C, FATES_STATE0, FATES_STATE1, GROUNDS, NE, P1, TOL, XA, XAY, Z,
                           compile_at, docket_A, docket_B, enforced, entitled_origins, excess,
                           in_region, outcome, residual, sat, scores, settle_outcome, settlement_at,
                           soft_gate, specialize, state_bundle, survivors, witness_at, row_of, occS,
                           T_B)


class TheCompileOutcome(unittest.TestCase):

    def test_conservation(self):
        # whatever the result, the obligations present are the state's bundle
        B = state_bundle(4, docket_A)
        for res in (("compiled", witness_at(4)), ("compiled", [F(0)] * 5), ("conflict", None), ("unknown",)):
            self.assertEqual(outcome(B, res)[2], B)

    def test_transparency(self):
        B = state_bundle(4, docket_A)
        self.assertEqual(outcome(B, ("compiled", witness_at(4)))[0], "enforced")
        self.assertEqual(outcome(B, ("compiled", [F(0)] * 5))[0], "withheld")   # unchecked witness
        self.assertEqual(outcome(B, ("conflict", None))[0], "withheld")         # conflict certificate
        self.assertEqual(outcome(B, ("unknown",))[0], "withheld")               # no result
        self.assertEqual(outcome([], ("unknown",))[0], "idle")                  # nothing to enforce

    def test_rows_held_are_present_rows(self):
        B = state_bundle(9, docket_A)
        for res in (("compiled", witness_at(9)), ("unknown",)):
            rows = compile_at(B, res)
            self.assertTrue(rows == B or rows == [])
        self.assertTrue(enforced(B, ("compiled", witness_at(9))))
        self.assertFalse(enforced(B, ("unknown",)))
        self.assertTrue(enforced([], ("unknown",)))  # vacuous


class ScenarioB(unittest.TestCase):

    def test_operative_before_withdrawn_after(self):
        for n in range(NE):
            self.assertIn(occS, survivors(GROUNDS, docket_B(n), settlement_at(n)))
            self.assertEqual(settle_outcome(settlement_at(n), occS.form), "kept")
        for n in range(NE, 12):
            self.assertNotIn(occS, survivors(GROUNDS, docket_B(n), settlement_at(n)))
            self.assertEqual(settle_outcome(settlement_at(n), occS.form), "rebutted")
        # the applicability never leaves in B; in A it leaves at the undercut
        self.assertEqual([o.id for o in survivors(GROUNDS, docket_B(9), settlement_at(9))], [1, 2, 4])
        self.assertEqual([o.id for o in survivors(GROUNDS, docket_A(9), settlement_at(9))], [1, 4])

    def test_consequent_false_antecedent_open(self):
        s = settlement_at(NE)
        self.assertIs(s[XAY], False)
        self.assertIs(s[3], False)
        self.assertIsNone(s[XA])
        self.assertTrue(in_region(state_bundle(9, docket_B), [F(1), F(1), F(0), F(0), F(1)]))

    def test_every_date_enforced(self):
        for n in range(12):
            self.assertTrue(enforced(state_bundle(n, docket_B), ("compiled", witness_at(n))))

    def test_contraposition_blocked(self):
        # the specialized strength row at date 9 reads 2/3 · XA ≤ 0; with XA ≥ 3/4 forced, infeasible
        s = settlement_at(9)
        strength = specialize(s, row_of(occS.form))
        self.assertEqual(strength, ([F(0), C["S"], F(0), F(0), F(0)], F(0)))
        B = state_bundle(9, docket_B) + [(("sub", 3), strength)]
        # a region point of the withdrawn system violates the kept row
        x = [F(1), F(1), F(0), F(0), F(1)]
        self.assertTrue(in_region(state_bundle(9, docket_B), x))
        self.assertFalse(sat(strength, x))
        # no point at all: the applicability row with X = 1 gives XA ≥ 3/4
        appl = [r for c, r in B if c == ("sub", 2)][0]
        self.assertEqual(appl, ([F(0), F(-1), F(0), F(0), F(0)], -C["A"]))
        for xa in (F(3, 4), F(7, 8), F(1)):
            self.assertFalse(sat(strength, [F(1), xa, F(0), F(0), F(1)]))


class TheSameQuestion(unittest.TestCase):

    def test_region_flips(self):
        # date 4: refraining ≤ 1/3 at the strength's binding point; date 9: refraining ≥ 3/4
        x4 = [F(1), F(3, 4), F(1, 2), F(1, 2), F(3, 4)]
        self.assertTrue(in_region(state_bundle(4, docket_B), x4))
        self.assertEqual(scores(P1, x4)[1], F(1, 4))
        x9 = [F(1), F(3, 4), F(0), F(0), F(1)]
        self.assertTrue(in_region(state_bundle(9, docket_B), x9))
        self.assertEqual(scores(P1, x9)[1], F(3, 4))

    def test_gate_after_at_the_enforced_extremes(self):
        # the enforced pin holds XAY ≤ tol, the enforced applicability row holds XA ≥ 3/4 − tol
        B = state_bundle(9, docket_B)
        pin = [r for c, r in B if c == ("settled", XAY) and r[0][XAY] == 1][0]
        appl = [r for c, r in B if c == ("sub", 2)][0]
        p = [F(1), C["A"] - TOL, TOL, F(0), F(1)]
        self.assertEqual(excess(pin, p), TOL)
        self.assertEqual(excess(appl, p), TOL)
        g = soft_gate(scores(P1, p), P1["pref"], P1["tau"], P1["delta"])
        self.assertEqual(g, [F(0), F(1)])

    def test_gate_before_bound(self):
        # κ · massCap · tol = 12 · 4/3 · 1/400 = 1/25
        self.assertEqual(F(12) * F(4, 3) * TOL, F(1, 25))


class Accounting(unittest.TestCase):

    def test_residual_restrict(self):
        full = residual({4, 9}, T_B)
        served = residual({4}, T_B)
        self.assertEqual(full, F(1, 4))
        self.assertEqual(served, F(1, 2))
        self.assertEqual(served - full, sum(T_B(e, 9) for e in (0, 1)))

    def test_progress_numbers(self):
        # Scenario A's protocol: ρ = (1/90000, 1/160000), λ = (1, 1), Γ = 12; Σ T ε = 3/40; residual 1/4
        rho_over_lam = (F(1, 90000) + F(1, 160000)) / 2
        self.assertLessEqual(rho_over_lam, F(1, 339) ** 2)
        bound = F(12, 339) + F(3, 40) + F(1, 4)
        self.assertLessEqual(bound, F(37, 100))
        self.assertLess(bound, 1)

    def test_entitlement_from_live_accounts(self):
        self.assertEqual(entitled_origins(FATES_STATE0), {0, 1})
        self.assertEqual(entitled_origins(FATES_STATE1), {1})
        self.assertEqual(Z, 4)


if __name__ == "__main__":
    unittest.main()
