"""Pressure pass §1–§3, §9–§11: common activation, its single void term, its typing
requirement, and the security-score form that needs no completion."""

import itertools
import unittest
from fractions import Fraction as Q

from src.world import principal_optimum, strategy_policy, paths, declared_mediated
from src.shop import never
from src.lift import lift
from src.fixtures import (ShopA, ShopG, ShopE, ShopE2, ShopE1Sever, pi_A, pi_E, pi_E_sever,
                          raw)
from src.analysis import (pointwise, kappa, rho, void, activation_independent, with_common,
                          void_common, premium_common, bound_common, bound, premium_def,
                          security_bypass, security_score, W)


def optimum_rule(game, L):
    _, strat = principal_optimum(game, L)
    return strategy_policy(strat, never)


def rows_of(table):
    rows = [{"p": p, "w_raw": wr, "w_app": wa, "w_act": wc, "c_raw": cr, "c_lift": cl, "z": i}
            for i, (p, wr, wa, wc, cr, cl) in enumerate(table)]
    return rows


class CommonActivation(unittest.TestCase):

    def test_G_exterior_activation_is_common_and_the_bound_has_one_void_term(self):
        g = ShopG()
        pi = raw(pi_A)
        L = lift(pi, g)
        rows = pointwise(g, pi, L, optimum_rule(g, L))
        self.assertTrue(activation_independent(rows))
        with_common(rows, lambda r: r["c_raw"])
        self.assertEqual(void_common(rows), Q(1, 5))
        self.assertEqual((kappa(rows), rho(rows)), (0, 0))
        top, bottom = (lambda r: g.LO + g.D), (lambda r: g.LO)
        # every pair of completions respects the common bound; the extreme pair attains
        # the void term exactly, so D·η is sharp under common activation
        for cr, cl in itertools.product((top, bottom), repeat=2):
            self.assertLessEqual(premium_common(rows, cr, cl), bound_common(rows, g.D))
        self.assertEqual(bound_common(rows, g.D), g.D * Q(1, 5))
        # the void fifth pays D; the activated four fifths pay the A comparison, −1/2
        self.assertEqual(premium_common(rows, top, bottom), g.D * Q(1, 5) + Q(4, 5) * Q(-1, 2))
        # the per-option bound on the same rows charges the void twice
        self.assertEqual(bound(rows, g.D), 2 * g.D * Q(1, 5))

    def test_common_void_witness(self):
        # the Lean `Witness.commonVoid` in the model's units
        rows = with_common(rows_of([(Q(1), Q(0), Q(0), Q(0), False, False)]),
                           lambda r: r["c_raw"])
        D = Q(1)
        self.assertEqual(premium_common(rows, lambda r: D, lambda r: Q(0)), D)
        self.assertEqual(bound_common(rows, D), D)
        self.assertEqual(bound(rows, D), 2 * D)

    def test_common_bound_on_a_grid(self):
        vals = [Q(0), Q(1, 2), Q(1)]
        D = Q(1)
        for wr, wa, wc, c in itertools.product(vals, vals, vals, (False, True)):
            rows = with_common(rows_of([(Q(1), wr, wa, wc, c, c)]), lambda r: r["c_raw"])
            for br in vals:
                for bl in vals:
                    if c and (br != wr or bl != wc):
                        continue
                    self.assertLessEqual(premium_common(rows, lambda r: br, lambda r: bl),
                                         bound_common(rows, D))

    def test_H_bypass_destroys_the_common_event(self):
        # E2: the raw option ends the evaluation on every path; the lift keeps it where
        # the principal declines.  Activation depends on the selection, so no common
        # event exists: the hypothesis that fails is activation independence.
        g = ShopE2()
        pi = raw(pi_E)
        L = lift(pi, g)
        rows = pointwise(g, pi, L, optimum_rule(g, L))
        self.assertFalse(activation_independent(rows))
        self.assertEqual([(r["z"][0], r["c_raw"], r["c_lift"]) for r in rows],
                         [("good", False, False), ("bad", False, True)])

    def test_E1_sealed_evaluator_is_common_and_security_scores_bind(self):
        g = ShopE()
        pi = raw(pi_E)
        L = lift(pi, g)
        rows = with_common(pointwise(g, pi, L, optimum_rule(g, L)), lambda r: r["c_raw"])
        self.assertTrue(activation_independent(rows))
        self.assertEqual(void_common(rows), 0)
        self.assertLessEqual(security_bypass(rows), kappa(rows) + rho(rows))
        self.assertEqual(security_bypass(rows), Q(-1, 4))

    def test_sealed_evaluator_can_still_be_reached_off_the_declaration(self):
        # E1 with an undeclared move that severs the evaluation channel: activation is
        # (vacuously) common — void on every path for both options — and the declaration
        # sees nothing.  Uniform incentive corrigibility fails outside the contained class.
        g = ShopE1Sever()
        pi = raw(pi_E_sever)
        L = lift(pi, g)
        rows = pointwise(g, pi, L, optimum_rule(g, L))
        self.assertTrue(activation_independent(rows))
        self.assertEqual(void(rows, "c_raw"), 1)
        self.assertEqual(void(rows, "c_lift"), 1)


class SecurityScores(unittest.TestCase):
    """§9–§10: the chooser's operative score is the price of the activated security; the
    bypass incentive in those scores has no void term."""

    def check(self, g, pi, rule=None):
        L = lift(pi, g)
        rule = rule or optimum_rule(g, L)
        rows = with_common(pointwise(g, pi, L, rule), lambda r: r["c_raw"])
        self.assertTrue(activation_independent(rows))
        self.assertLessEqual(security_bypass(rows), kappa(rows) + rho(rows))
        return rows

    def test_A_security_bypass_is_negative(self):
        rows = self.check(ShopA(), raw(pi_A))
        self.assertEqual(security_bypass(rows), Q(-1, 2))

    def test_G_security_bypass_ignores_the_void_branch(self):
        rows = self.check(ShopG(), raw(pi_A))
        # 4/5 of the A comparison; the void fifth contributes zero to both scores
        self.assertEqual(security_bypass(rows), Q(4, 5) * Q(-1, 2))

    def test_security_scores_versus_completions(self):
        # on G, a completion-valued agent can prefer the raw option by up to D·η while
        # the security-score agent never does
        g = ShopG()
        pi = raw(pi_A)
        L = lift(pi, g)
        rows = with_common(pointwise(g, pi, L, optimum_rule(g, L)), lambda r: r["c_raw"])
        self.assertGreater(premium_common(rows, lambda r: g.LO + g.D, lambda r: g.LO), 0)
        self.assertLess(security_bypass(rows), 0)


if __name__ == "__main__":
    unittest.main()
