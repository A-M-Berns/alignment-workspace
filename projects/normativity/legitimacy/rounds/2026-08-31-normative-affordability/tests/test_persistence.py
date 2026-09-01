"""Exact checks for the persistence characterization and its scheduler."""
from fractions import Fraction
import unittest

import persistence as P


class TheExactOptimum(unittest.TestCase):
    """`max { sum a_t : conservative charge <= B } = B^2 / (min q)^2`, attained by
    putting the whole budget on one least-friction date."""

    def test_the_optimum_is_the_vertex(self):
        q = [Fraction(1), Fraction(1, 3), Fraction(1, 2)]
        budget = Fraction(2)
        best = P.optimal_concentration(q, budget)
        self.assertEqual(best, [Fraction(0), Fraction(6), Fraction(0)])
        self.assertEqual(P.charge(q, best), budget)
        self.assertEqual(P.cumulative_authority(best), Fraction(36))
        self.assertEqual(P.max_authority(q, budget), Fraction(36))

    def test_no_split_beats_it(self):
        q = [Fraction(1), Fraction(1, 3), Fraction(1, 2)]
        budget = Fraction(2)
        cap = P.max_authority(q, budget)
        grid = [Fraction(k, 6) for k in range(0, 13)]
        for x0 in grid:
            for x1 in grid:
                for x2 in grid:
                    x = [x0, x1, x2]
                    if P.charge(q, x) <= budget:
                        self.assertLessEqual(P.cumulative_authority(x), cap)

    def test_the_optimum_tracks_the_running_minimum(self):
        q = P.sparse_friction(16)
        budget = Fraction(1)
        caps = [P.max_authority(q[:n], budget) for n in (1, 2, 4, 8, 16)]
        for earlier, later in zip(caps, caps[1:]):
            self.assertGreaterEqual(later, earlier)
        self.assertGreater(caps[-1], Fraction(10 ** 4))


class PersistenceIffTheFrictionDipsToZero(unittest.TestCase):
    """Sufficiency by a sparse concentration; necessity because a friction floor
    forces the authority to be summable."""

    def test_sparse_low_friction_dates_carry_unbounded_authority(self):
        for horizon in (16, 64, 256):
            q = P.sparse_friction(horizon)
            budget = Fraction(1)
            x = P.doubling_schedule(q, budget)
            self.assertLessEqual(P.charge(q, x), budget)
            self.assertGreater(P.cumulative_authority(x), Fraction(0))
        totals = [P.cumulative_authority(P.doubling_schedule(P.sparse_friction(h),
                                                             Fraction(1)))
                  for h in (16, 64, 256)]
        for earlier, later in zip(totals, totals[1:]):
            self.assertGreater(later, earlier)

    def test_a_friction_floor_caps_the_lifetime_authority(self):
        """With `q_t >= q0`, `sum x <= B/q0`, so `sum x^2 <= (B/q0)^2` at every
        horizon: the authority is bounded however the schedule is chosen."""
        floor, budget = Fraction(1, 4), Fraction(1)
        for horizon in (8, 64, 512):
            q = P.flat_friction(horizon, floor)
            self.assertEqual(P.max_authority(q, budget), Fraction(16))
            x = P.doubling_schedule(q, budget)
            self.assertLessEqual(P.cumulative_authority(x), Fraction(16))

    def test_the_bound_is_uniform_in_the_horizon(self):
        floor, budget = Fraction(1, 4), Fraction(1)
        caps = [P.max_authority(P.flat_friction(h, floor), budget)
                for h in (8, 64, 512, 4096)]
        self.assertEqual(caps, [Fraction(16)] * 4)


class TheCausalSchedulerLosesNothing(unittest.TestCase):
    """A rule seeing the friction only at its own date achieves persistence
    whenever an offline schedule can."""

    def test_every_trigger_contributes_at_least_a_fixed_amount(self):
        budget = Fraction(1)
        q = P.sparse_friction(64)
        x = P.doubling_schedule(q, budget)
        contributions = [xi * xi for xi in x if xi > 0]
        self.assertEqual(len(contributions), P.triggers(q))
        for c in contributions:
            self.assertGreaterEqual(c, budget ** 2 / 4)

    def test_it_stays_inside_the_budget(self):
        for horizon in (16, 64, 256):
            q = P.sparse_friction(horizon)
            x = P.doubling_schedule(q, Fraction(1))
            self.assertLessEqual(P.charge(q, x), Fraction(1))

    def test_it_triggers_only_finitely_often_under_a_friction_floor(self):
        q = P.flat_friction(512, Fraction(1, 4))
        self.assertEqual(P.triggers(q), 3)      # thresholds 1, 1/2, 1/4

    def test_it_triggers_at_every_threshold_when_friction_decays(self):
        q = P.decaying_friction(32)
        self.assertEqual(P.triggers(q), 32)


class SignedAccountBeatsTheConservativeCertificate(unittest.TestCase):
    """A norm the reasoner already satisfies costs nothing however deep its
    exclusion of live worlds, while the conservative charge diverges."""

    def _trajectory(self, horizon):
        x = [Fraction(1)] * horizon             # a_t = 1 at every date
        defect = [Fraction(0)] * horizon        # the price satisfies the row
        misfit = [Fraction(3, 4)] * horizon     # a live world does not
        return x, defect, misfit

    def test_the_realized_account_is_exactly_zero(self):
        for horizon in (8, 64, 512):
            x, d, s = self._trajectory(horizon)
            self.assertEqual(P.realized_account(x, d, s), Fraction(0))

    def test_the_conservative_charge_diverges(self):
        floor = Fraction(3, 4)
        charges = []
        for horizon in (8, 64, 512):
            x, _, _ = self._trajectory(horizon)
            charges.append(P.conservative_charge(P.flat_friction(horizon, floor),
                                                 x))
        self.assertEqual(charges, [Fraction(6), Fraction(48), Fraction(384)])

    def test_the_authority_diverges_with_the_account_at_zero(self):
        totals = [P.cumulative_authority(self._trajectory(h)[0])
                  for h in (8, 64, 512)]
        self.assertEqual(totals, [Fraction(8), Fraction(64), Fraction(512)])

    def test_a_single_violating_date_is_what_costs(self):
        x = [Fraction(1)] * 4
        d = [Fraction(0), Fraction(0), Fraction(1, 4), Fraction(0)]
        s = [Fraction(3, 4)] * 4
        self.assertEqual(P.realized_account(x, d, s), Fraction(-1, 8))


class TheScalarSlackIsNotSufficientState(unittest.TestCase):
    """Two profiles with the same minimum have different futures once settlement
    removes the world that was worst."""

    def setUp(self):
        self.floor = Fraction(1)
        self.thin = P.Profile({"w1": Fraction(0), "w2": Fraction(0)},
                              ["w1", "w2"])
        self.fat = P.Profile({"w1": Fraction(0), "w2": Fraction(10)},
                             ["w1", "w2"])

    def test_the_two_profiles_have_equal_slack(self):
        self.assertEqual(self.thin.slack(self.floor), Fraction(1))
        self.assertEqual(self.fat.slack(self.floor), Fraction(1))

    def test_settlement_separates_them(self):
        thin = self.thin.settle(["w2"])
        fat = self.fat.settle(["w2"])
        self.assertEqual(thin.slack(self.floor), Fraction(1))
        self.assertEqual(fat.slack(self.floor), Fraction(11))

    def test_the_viable_authority_differs_after_settlement(self):
        """Route B allocates `slack^2 / (m D^2)`, so an eleven-fold slack is a
        hundred-and-twenty-one-fold authority."""
        budget, depth = Fraction(1), Fraction(1)
        thin = self.thin.settle(["w2"]).slack(self.floor)
        fat = self.fat.settle(["w2"]).slack(self.floor)
        self.assertEqual((fat ** 2) / (budget * depth ** 2), Fraction(121))
        self.assertEqual((thin ** 2) / (budget * depth ** 2), Fraction(1))

    def test_a_settlement_that_removes_nothing_leaves_them_equal(self):
        thin = self.thin.settle(["w1", "w2"])
        fat = self.fat.settle(["w1", "w2"])
        self.assertEqual(thin.slack(self.floor), fat.slack(self.floor))


class ManyReasonsDoNotCompeteForPersistence(unittest.TestCase):
    """Splitting the lifetime budget geometrically leaves every reason's
    persistence intact, because the characterization does not mention the
    budget."""

    def test_each_reason_still_diverges_on_its_own_tranche(self):
        reasons = 5
        horizon = 256
        q = P.sparse_friction(horizon)
        totals = []
        for r in range(reasons):
            share = Fraction(1, 2 ** (r + 1))
            x = P.doubling_schedule(q, share)
            totals.append(P.cumulative_authority(x))
            self.assertLessEqual(P.charge(q, x), share)
        self.assertEqual(sum((Fraction(1, 2 ** (r + 1))
                              for r in range(reasons)), Fraction(0)),
                         Fraction(31, 32))
        for value in totals:
            self.assertGreater(value, Fraction(0))

    def test_the_cap_scales_with_the_square_of_the_share(self):
        q = P.sparse_friction(64)
        full = P.max_authority(q, Fraction(1))
        half = P.max_authority(q, Fraction(1, 2))
        self.assertEqual(full / half, Fraction(4))


if __name__ == "__main__":
    unittest.main()
