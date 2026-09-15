"""Directional activation mismatch: the identity, the exact and directional bounds,
sharpness, the refuted marginal-rate bound, and the engine-derived fixtures."""

import unittest
from fractions import Fraction as Q

from src import mismatch as M
from src.model import load


def rows_of(game, pi_raw, rule=None):
    """Per-path rows with the protected values shifted by the band floor `LO`, so the
    per-option securities `c · (w − LO)` take values in `[0, D]`."""
    m = load()
    C = m["lift"].corrigibilize(pi_raw, game)
    if rule is None:
        _, strat = m["world"].principal_optimum(game, C)
        rule = m["world"].strategy_policy(strat, m["shop"].never)
    rows = m["analysis"].pointwise(game, pi_raw, C, rule)
    values = [r[k] for r in rows for k in ("w_raw", "w_app", "w_act")]
    lo, D = min(values), max(values) - min(values)
    for r in rows:
        for k in ("w_raw", "w_app", "w_act"):
            r[k] = r[k] - lo
            assert Q(0) <= r[k] <= D
    return rows, D


class Identity(unittest.TestCase):

    SPEC = [
        # p, w_raw, w_app, w_act, c_raw, c_lift, delta
        (Q(1, 4), 4, 4, 2, 1, 1, 0),
        (Q(1, 4), 3, 3, 3, 1, 0, 0),
        (Q(1, 4), 2, 1, 1, 0, 1, 1),
        (Q(1, 4), 1, 1, 1, 0, 0, 0),
    ]

    def test_pointwise_identity(self):
        for r in M.synthetic(self.SPEC):
            self.assertEqual(M.U_raw(r) - M.U_corr(r), M.identity_rhs(r))

    def test_exact_le_directional(self):
        rows = M.synthetic(self.SPEC)
        L, D = Q(1), Q(4)
        self.assertLessEqual(M.bypass(rows), M.exact_bound(rows, L))
        self.assertLessEqual(M.exact_bound(rows, L), M.directional_bound(rows, L, D))

    def test_reverse_mismatch_is_free(self):
        rows = M.synthetic([(1, 0, 0, 3, 0, 1, 0)])
        self.assertEqual(M.bypass(rows), Q(-3))
        self.assertEqual(M.mismatch_mass(rows), Q(0))
        self.assertEqual(M.reverse_mass(rows), Q(1))
        self.assertEqual(M.directional_bound(rows, Q(1), Q(3)), Q(0))


class Sharpness(unittest.TestCase):

    def test_D_attained(self):
        # one world: raw activated, corr not, w_raw = D; the premium is exactly D·M
        D = Q(7)
        rows = M.synthetic([(1, D, D, D, 1, 0, 0)])
        self.assertEqual(M.bypass(rows), D)
        self.assertEqual(M.directional_bound(rows, Q(1), D), D)
        self.assertEqual(M.mismatch_mass(rows), Q(1))

    def test_exact_bound_attained_below_D(self):
        D = Q(7)
        rows = M.synthetic([(1, 2, 2, 2, 1, 0, 0)])
        self.assertEqual(M.bypass(rows), Q(2))
        self.assertEqual(M.exact_bound(rows, Q(1)), Q(2))
        self.assertEqual(M.directional_bound(rows, Q(1), D), D)

    def test_tiny_mismatch(self):
        eps = Q(1, 1000)
        D = Q(1)
        rows = M.synthetic([(1 - eps, 1, 1, 1, 1, 1, 0), (eps, 1, 1, 1, 1, 0, 0)])
        self.assertEqual(M.bypass(rows), eps)
        self.assertEqual(M.directional_bound(rows, Q(1), D), D * eps)


class MarginalRefuted(unittest.TestCase):

    def test_marginal_difference_zero_but_premium_positive(self):
        D = Q(2)
        rows = M.synthetic([(Q(1, 2), D, D, 0, 1, 0, 0), (Q(1, 2), 0, 0, 0, 0, 1, 0)])
        self.assertEqual(M.marginal_difference(rows), Q(0))
        self.assertEqual(M.mismatch_mass(rows), Q(1, 2))
        self.assertEqual(M.bypass(rows), D / 2)
        self.assertLess(M.marginal_bound(rows, Q(1), D), M.bypass(rows))
        self.assertLessEqual(M.bypass(rows), M.directional_bound(rows, Q(1), D))

    def test_selection_dependent_value_irrelevant_difference(self):
        # raw-only activation on a path where the raw value is 0: charged D by the
        # directional bound, 0 by the exact bound, and the premium is 0
        D = Q(3)
        rows = M.synthetic([(1, 0, 0, 0, 1, 0, 0)])
        self.assertEqual(M.bypass(rows), Q(0))
        self.assertEqual(M.exact_bound(rows, Q(1)), Q(0))
        self.assertEqual(M.directional_bound(rows, Q(1), D), D)


class EngineFixtures(unittest.TestCase):

    def check(self, game, pi_raw, rule=None):
        rows, D = rows_of(game, pi_raw, rule)
        self.assertTrue(M.lipschitz_ok(rows, game.L))
        self.assertLessEqual(M.bypass(rows), M.exact_bound(rows, game.L))
        self.assertLessEqual(M.exact_bound(rows, game.L), M.directional_bound(rows, game.L, D))
        return rows, D

    def test_common_activation_reduces_to_sharp(self):
        m = load()
        F = m["fixtures"]
        for g, pf in ((F.ShopA_AF(), F.pi_A), (F.ShopE_AF(), F.pi_E), (F.ShopB_AF(), F.pi_B)):
            rows, D = self.check(g, F.raw(pf))
            self.assertTrue(M.activation_independent(rows))
            self.assertEqual(M.mismatch_mass(rows), Q(0))
            self.assertEqual(M.directional_bound(rows, g.L, D), M.common_sharp_bound(rows, g.L))

    def test_raw_evaluator_destruction_E2(self):
        """The raw install ends the evaluation on every path.  Under the optimum rule the
        corrigibilized option installs too (both void, common activation, premium 0);
        under the always-decline rule only the corrigibilized option's evaluation
        survives: reverse mismatch, charged nothing, premium negative."""
        m = load()
        F = m["fixtures"]
        g = F.ShopE2_AF()
        rows, _ = self.check(g, F.raw(F.pi_E))
        self.assertTrue(M.activation_independent(rows))
        self.assertEqual(M.bypass(rows), Q(0))
        rows, D = self.check(g, F.raw(F.pi_E), m["lift"].decline_all)
        self.assertEqual(M.mismatch_mass(rows), Q(0))
        self.assertEqual(M.reverse_mass(rows), Q(1))
        self.assertLess(M.bypass(rows), Q(0))
        self.assertEqual(M.directional_bound(rows, g.L, D), Q(0))
        self.assertFalse(M.activation_independent(rows))

    def test_time_critical_evaluation_B(self):
        """B1 with an evaluation that can be answered only if the contract is still there
        or was signed: the raw option activates on every path, the corrigibilized option
        only where the opportunity stays.  The exact bound is attained."""
        m = load()
        F = m["fixtures"]

        class TimeCritical(F.ShopB_AF):
            def alive(self, traj):
                f = traj.final
                return bool(f.get("signed", False)) or bool(f.get("opp", True))

        g = TimeCritical()
        rows, D = self.check(g, F.raw(F.pi_B))
        self.assertFalse(M.activation_independent(rows))
        self.assertEqual(M.mismatch_mass(rows), Q(1, 4))
        # the raw option signs (the top of the band, D = 4) on the expired path where
        # only it activates: bypass, exact bound and directional bound all equal D/4
        self.assertEqual(D, Q(4))
        self.assertEqual(M.bypass(rows), D / 4)
        self.assertEqual(M.exact_bound(rows, g.L), D / 4)
        self.assertEqual(M.directional_bound(rows, g.L, D), D / 4)

    def test_manipulation_corrigible_not_authored_D(self):
        """The captured principal approves the lie-carrying proposal: the pair satisfies
        the inequality with no mismatch, and the theorem says nothing about manipulation."""
        m = load()
        F = m["fixtures"]
        g = F.ShopD_AF()
        rows, D = self.check(g, F.raw(F.pi_D_raw), F.rule_naive)
        self.assertTrue(M.activation_independent(rows))
        self.assertLessEqual(M.bypass(rows), M.directional_bound(rows, g.L, D))
        self.assertEqual(M.bypass(rows), Q(0))


if __name__ == "__main__":
    unittest.main()
