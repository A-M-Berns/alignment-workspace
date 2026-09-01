"""Exact checks separating allocated service from realized force."""
from fractions import Fraction
import unittest

import service as S


class RealizedForceIsNotService(unittest.TestCase):
    """Three failures of `w = beta d` as the service variable, of increasing
    severity."""

    def test_perfect_compliance_leaves_the_force_measure_undefined(self):
        traj = S.perfect_compliance(12)
        self.assertEqual(traj.allocation_total(), Fraction(12))
        self.assertEqual(traj.force_total(), Fraction(0))
        with self.assertRaises(ValueError):
            traj.force_measure()
        # The allocation measure exists and is uniform.
        self.assertEqual(traj.allocation_measure(), [Fraction(1, 12)] * 12)

    def test_successful_learning_looks_like_starvation_in_force_mass(self):
        forces, allocations = [], []
        for horizon in (4, 8, 16, 32):
            traj = S.successful_learning(horizon)
            forces.append(traj.force_total())
            allocations.append(traj.allocation_total())
        self.assertEqual(allocations, [Fraction(4), Fraction(8), Fraction(16),
                                       Fraction(32)])
        # Force mass converges to 2 and is bounded by it at every horizon.
        for f in forces:
            self.assertLess(f, Fraction(2))
        for earlier, later in zip(forces, forces[1:]):
            self.assertGreater(later, earlier)

    def test_the_defect_still_vanishes_under_the_allocation_measure(self):
        values = [S.successful_learning(h).expect_defect()
                  for h in (4, 8, 16, 32)]
        for earlier, later in zip(values, values[1:]):
            self.assertLess(later, earlier)
        self.assertLess(values[-1], Fraction(1, 15))

    def test_equal_authority_and_unequal_defect_give_unequal_force(self):
        """Two dates, the same allocated authority, different violations. The
        force measure says the harder date got more service."""
        traj = S.ServiceTrajectory([Fraction(1), Fraction(1)],
                                   [Fraction(1, 10), Fraction(9, 10)])
        self.assertEqual(traj.allocation_measure(),
                         [Fraction(1, 2), Fraction(1, 2)])
        self.assertEqual(traj.force_measure(),
                         [Fraction(1, 10), Fraction(9, 10)])


class ModulusGivesQuadraticProgress(unittest.TestCase):
    """`sum a d^2 <= sum budget` per date, then Cauchy-Schwarz."""

    def test_the_saturating_trajectory_meets_the_modulus_with_equality(self):
        horizon = 16
        traj = S.saturating(horizon)
        budgets = [Fraction(1)] * horizon
        self.assertTrue(traj.obeys_modulus(budgets))
        self.assertEqual(traj.work_total(), Fraction(horizon))

    def test_mean_square_defect_vanishes_at_the_stated_rate(self):
        for horizon in (4, 16, 64):
            traj = S.saturating(horizon)
            allocation = Fraction(horizon * (horizon + 1) * (2 * horizon + 1), 6)
            self.assertEqual(traj.allocation_total(), allocation)
            self.assertEqual(traj.expect_square(), Fraction(horizon) / allocation)
            self.assertEqual(traj.expect_square(),
                             Fraction(6, (horizon + 1) * (2 * horizon + 1)))

    def test_cauchy_schwarz_bounds_the_mean_defect(self):
        for horizon in (4, 16, 64):
            traj = S.saturating(horizon)
            mean = traj.expect_defect()
            self.assertLessEqual(mean * mean, traj.expect_square())

    def test_the_two_directions_are_equivalent_for_a_bounded_defect(self):
        """`E[d]^2 <= E[d^2] <= D E[d]`, so the quadratic and linear forms
        vanish together; only the rate differs."""
        for horizon in (4, 16, 64):
            traj = S.saturating(horizon)
            cap = max(traj.defect)
            self.assertLessEqual(traj.expect_defect() ** 2, traj.expect_square())
            self.assertLessEqual(traj.expect_square(), cap * traj.expect_defect())

    def test_a_summable_work_series_gives_the_faster_rate(self):
        """`sum a d^2 <= U` bounded gives `E[d^2] <= U/A_N`, which is the
        compatible-world case."""
        for horizon in (8, 32, 128):
            traj = S.successful_learning(horizon)
            self.assertLess(traj.work_total(), Fraction(4, 3))
            self.assertLess(traj.expect_square(), Fraction(4, 3) / Fraction(horizon))


class FrictionResidual(unittest.TestCase):
    """A norm whose misfit does not vanish keeps the defect at the misfit."""

    def test_the_defect_does_not_fall_below_the_misfit(self):
        floor = Fraction(1, 5)
        for horizon in (8, 32, 128):
            traj = S.friction_floor(horizon, floor)
            self.assertEqual(traj.expect_defect(), floor)
            self.assertEqual(traj.expect_square(), floor * floor)
            self.assertEqual(traj.expect_misfit_square(), floor * floor)

    def test_the_account_is_exactly_zero_at_the_friction_floor(self):
        """`d = s` is the second root of `a d (d - s)`: force costs nothing and
        buys nothing, which is why the floor is where the trajectory rests."""
        for horizon in (8, 32):
            traj = S.friction_floor(horizon, Fraction(1, 5))
            self.assertEqual(traj.account(), Fraction(0))

    def test_the_work_bound_forces_the_defect_toward_the_misfit(self):
        """With `V_N <= U` the work is at most `U` plus the charge, so
        `E[d^2] <= U/A_N + E[d s]`."""
        for horizon in (8, 32, 128):
            traj = S.successful_learning(horizon)
            slack = traj.account()
            self.assertEqual(traj.work_total(), slack + traj.charge_total())
            self.assertLessEqual(traj.expect_square(),
                                 slack / traj.allocation_total()
                                 + traj.charge_total() / traj.allocation_total())


class CapacityInAuthoritySpace(unittest.TestCase):
    """Divergent allocated service on a finite lifetime liability budget."""

    def _schedule(self, horizon):
        # Per-date allowance 1/(t+1)^2 (summable), slack-plus-volume 1, and an
        # exclusion depth halving each date.
        budgets = [Fraction(1)] * horizon
        allowances = [Fraction(1, (t + 1) ** 2) for t in range(horizon)]
        depths = [Fraction(1, 4 ** t) for t in range(horizon)]
        return budgets, allowances, depths

    def test_the_authority_cap_diverges_while_the_allowance_is_summable(self):
        horizon = 12
        budgets, allowances, depths = self._schedule(horizon)
        caps = [S.capacity(b, a, d)
                for b, a, d in zip(budgets, allowances, depths)]
        self.assertEqual(caps[0], Fraction(1))
        self.assertEqual(caps[-1], Fraction(16 ** 11, 12 ** 4))
        for earlier, later in zip(caps[2:], caps[3:]):
            self.assertGreater(later, earlier)
        self.assertLess(sum(allowances, Fraction(0)), Fraction(2))
        self.assertGreater(sum(caps, Fraction(0)), Fraction(10 ** 6))

    def test_a_trajectory_at_the_cap_has_divergent_service_and_bounded_charge(self):
        horizon = 12
        budgets, allowances, depths = self._schedule(horizon)
        alloc = [S.capacity(b, a, d)
                 for b, a, d in zip(budgets, allowances, depths)]
        # Violations at the modulus ceiling would be irrational; take the
        # largest rational under it, d_t = the depth, which is admissible
        # because a_t d_t^2 <= budget_t holds by construction of the cap.
        defect = list(depths)
        traj = S.ServiceTrajectory(alloc, defect, depths)
        self.assertTrue(traj.obeys_modulus(budgets))
        self.assertGreater(traj.allocation_total(), Fraction(10 ** 6))
        self.assertLess(traj.charge_total(), Fraction(2))

    def test_liability_grows_like_the_square_root_of_authority(self):
        """`a d <= sqrt(a * budget)`, so doubling authority at the modulus
        ceiling multiplies the realized force by `sqrt(2)`, not by `2`."""
        budget = Fraction(1)
        for alloc in (Fraction(1), Fraction(4), Fraction(16), Fraction(64)):
            square = S.conformance_ceiling(alloc, budget)
            force_square = alloc * alloc * square
            self.assertEqual(force_square, alloc * budget)


if __name__ == "__main__":
    unittest.main()
