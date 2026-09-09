"""Consolidation pass: the sharpened security-score bound, the uniform T4 over a family of
raw continuations, and the sealed-comparison-by-sequencing fixture."""

import unittest
from fractions import Fraction as Q

from src.world import principal_optimum, strategy_policy, paths
from src.shop import never
from src.lift import corrigibilize, approve_all
from src.fixtures import (ShopA_AF, ShopE_AF, ShopB_AF, ShopE1Sever_AF, ShopSeq, ShopF_AF,
                          pi_A, pi_E, pi_B, pi_E_sever, pi_F, raw)
from src.analysis import (pointwise, with_common, security_bypass, bound_sharp, kappa, rho,
                          delta, activation_independent, void, phi_corr, pos, W)


def rule_of(g, C):
    _, strat = principal_optimum(g, C)
    return strategy_policy(strat, never)


class SharpenedScoreBound(unittest.TestCase):

    def check(self, g, pi, common=lambda r: r["c_raw"]):
        C = corrigibilize(pi, g)
        rows = with_common(pointwise(g, pi, C, rule_of(g, C)), common)
        self.assertTrue(activation_independent(rows))
        self.assertLessEqual(security_bypass(rows), bound_sharp(rows, g.L))
        return rows

    def test_A_E_B(self):
        for g, pf in ((ShopA_AF(), pi_A), (ShopE_AF(), pi_E), (ShopB_AF(), pi_B)):
            self.check(g, raw(pf))

    def test_void_worlds_are_not_charged(self):
        # a common event that fails on some paths: the sharpened bound omits their δ and ρ
        class Half(ShopA_AF):
            def alive(self, traj):
                return traj.states()[1].harm == "good"
        g = Half()
        pi = raw(pi_A)
        C = corrigibilize(pi, g)
        rows = with_common(pointwise(g, pi, C, rule_of(g, C)), lambda r: r["c_raw"])
        self.assertTrue(activation_independent(rows))
        self.assertEqual(void(rows, "c_raw"), Q(1, 4))
        loose = g.L * delta(rows) + rho(rows)
        self.assertLessEqual(bound_sharp(rows, g.L), loose)
        self.assertLessEqual(security_bypass(rows), bound_sharp(rows, g.L))


class UniformT4(unittest.TestCase):

    def test_supremum_over_a_family(self):
        g = ShopA_AF()
        family = [
            raw(pi_A),
            raw(lambda s, t: ("work", ("raw", "cut")) if t == 1 and s.wire else ("work", None)),
            raw(lambda s, t: ("work", ("raw", "cut")) if t == 2 and s.wire else ("work", None)),
            raw(lambda s, t: ("work", None)),
            raw(lambda s, t: ("idle", ("raw", "cut")) if s.wire else ("idle", None)),
        ]
        rules = [rule_of(g, corrigibilize(pi, g)) for pi in family]
        phi, bnd, gaps, bounds = phi_corr(g, family, rules)
        for gap, b in zip(gaps, bounds):
            self.assertLessEqual(gap, b)
        self.assertLessEqual(phi, bnd)
        # the positive gaps belong to the time-critical members (a cut on the last step
        # cannot be mediated in time); the others score no higher than their
        # corrigibilization
        self.assertEqual([gap > 0 for gap in gaps], [False, False, True, False, False])
        self.assertEqual((phi, bnd), (Q(1, 2), Q(1)))

    def test_foreclosing_is_in_the_family_with_a_large_bound(self):
        # a time-critical opportunity: the positive bound is exposed, not excluded
        g = ShopB_AF()
        pi = raw(pi_B)
        C = corrigibilize(pi, g)
        rows = with_common(pointwise(g, pi, C, rule_of(g, C)), lambda r: r["c_raw"])
        self.assertEqual(security_bypass(rows), Q(1))
        self.assertEqual(bound_sharp(rows, g.L), Q(1))


class SealedBySequencing(unittest.TestCase):

    def test_hindsight_evaluation_is_severed(self):
        g = ShopE1Sever_AF()
        pi = raw(pi_E_sever)
        C = corrigibilize(pi, g)
        rows = pointwise(g, pi, C, rule_of(g, C))
        self.assertEqual((void(rows, "c_raw"), void(rows, "c_lift")), (1, 1))

    def test_sequenced_settlement_is_independent_of_every_candidate(self):
        g = ShopSeq()
        pi = raw(pi_E_sever)
        C = corrigibilize(pi, g)
        rows = with_common(pointwise(g, pi, C, rule_of(g, C)), lambda r: r["c_raw"])
        self.assertTrue(activation_independent(rows))
        self.assertEqual(void(rows, "c_raw"), 0)
        # the price: the security settles to the principal's ex-ante judgment, which for
        # the same moves is the expectation over the revelation; its total agrees with the
        # hindsight expectation, its conditional information is gone
        ex_ante = sum((pr * g.w_ex_ante(tr) for tr, pr in paths(g, pi, never)), Q(0))
        self.assertEqual(ex_ante, W(rows, "w_raw"))
        for tr, _ in paths(g, pi, never):
            self.assertNotEqual(g.w_ex_ante(tr), g.w(g.proj(tr)))

    def test_effect_incompleteness_is_untouched_by_sequencing(self):
        # sequencing seals the comparison; it does not make the raw policy corrigible
        from src.corrigibility import corrigible, phi_halt
        g = ShopSeq()
        pi = raw(pi_E_sever)
        self.assertFalse(corrigible(g, pi, never)[0])


if __name__ == "__main__":
    unittest.main()
