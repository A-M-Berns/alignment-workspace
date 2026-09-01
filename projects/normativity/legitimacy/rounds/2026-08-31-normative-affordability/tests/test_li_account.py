"""Exact checks for the traderized authority account.

These are the fixtures the follow-up audit turns on: the value identity, the
refutation of pointwise self-financing as a necessary condition, the difference
between the signed cumulative account and the sum of per-date worst cases, and
the asymmetry between the world quantifier Progress uses and the one liability
uses.
"""
from fractions import Fraction
import unittest

import li_account as L


ONE, ZERO = [Fraction(1)], [Fraction(0)]


class ValueIdentity(unittest.TestCase):
    """`value = work - charge` whenever every violated row excludes the world,
    and `value >= work - charge` always."""

    def test_identity_on_the_alternating_fixture(self):
        traj = L.alternating_norm(8)
        for price, step in traj.steps:
            excluded = [w for w in traj.worlds if step.rows[0].excludes(w)]
            for world in excluded:
                self.assertEqual(step.value(price, world),
                                 step.work(price) - step.charge(price, world))

    def test_inequality_holds_at_every_world(self):
        traj = L.alternating_norm(8)
        for price, step in traj.steps:
            for world in traj.worlds:
                self.assertGreaterEqual(
                    step.value(price, world),
                    step.work(price) - step.charge(price, world))

    def test_a_world_the_row_admits_is_never_charged(self):
        traj = L.compatible_world(4)
        price, step = traj.steps[0]
        self.assertEqual(step.charge(price, ONE), Fraction(0))
        self.assertGreater(step.charge(price, ZERO), Fraction(0))


class PointwiseSelfFinancingIsNotNecessary(unittest.TestCase):
    """Every date shows a real loss in a live world, unbounded force is applied,
    and the account stays inside a fixed band. This refutes the claim that
    persistent service requires each control to be robustly non-loss-making."""

    def test_every_date_has_a_strictly_positive_robust_loss(self):
        traj = L.alternating_norm(12)
        losses = traj.per_date_robust_loss()
        self.assertEqual(len(losses), 12)
        for loss in losses:
            self.assertEqual(loss, Fraction(1))

    def test_the_account_stays_inside_a_fixed_band(self):
        for horizon in (2, 8, 32, 128):
            traj = L.alternating_norm(horizon)
            self.assertEqual(traj.liability(), Fraction(1))

    def test_total_force_applied_diverges(self):
        sizes = [L.alternating_norm(h).total_size() for h in (2, 8, 32, 128)]
        self.assertEqual(sizes, [Fraction(4), Fraction(16), Fraction(64),
                                 Fraction(256)])

    def test_the_per_date_certificate_diverges_where_the_account_does_not(self):
        """The sum of per-date worst cases is the conservative route, and here it
        is conservative by an unbounded factor."""
        for horizon in (8, 32, 128):
            traj = L.alternating_norm(horizon)
            self.assertEqual(traj.certificate_charge(), Fraction(horizon))
            self.assertEqual(traj.liability(), Fraction(1))


class DecayingDepthIsSafeAndFixedDepthIsNot(unittest.TestCase):
    """A region excluding the sole live world at every date is affordable when
    the exclusion depth decays, and unaffordable when it does not."""

    def test_every_date_is_a_real_loss_in_the_only_live_world(self):
        traj = L.decaying_depth(8)
        for price, step in traj.steps:
            self.assertTrue(step.rows[0].excludes(ONE))
            self.assertLess(step.value(price, ONE), Fraction(0))

    def test_the_account_converges(self):
        bounds = [L.decaying_depth(h).liability() for h in (4, 8, 16, 32)]
        for earlier, later in zip(bounds, bounds[1:]):
            self.assertGreaterEqual(later, earlier)
        self.assertLess(bounds[-1], Fraction(1, 4))

    def test_fixed_depth_diverges(self):
        bounds = [L.fixed_depth(h).liability() for h in (4, 8, 16, 32)]
        self.assertEqual(bounds, [Fraction(1, 4), Fraction(1, 2),
                                  Fraction(1), Fraction(2)])


class ProgressAndLiabilityUseOppositeQuantifiers(unittest.TestCase):
    """Cumulative force work is bounded by the account at the *best* live world;
    liability is the account at the worst. One compatible world does the first
    job and not the second."""

    def test_the_compatible_world_never_charges_and_pays_at_least_the_work(self):
        traj = L.compatible_world(6)
        self.assertEqual(traj.charge_total(ONE), Fraction(0))
        self.assertEqual(traj.work_total(), Fraction(3, 8))
        self.assertEqual(traj.cumulative_value(ONE), Fraction(3, 4))
        self.assertGreaterEqual(traj.cumulative_value(ONE), traj.work_total())

    def test_liability_at_the_other_world_grows_without_bound(self):
        values = [L.compatible_world(h).liability() for h in (4, 8, 16, 32)]
        for earlier, later in zip(values, values[1:]):
            self.assertGreater(later, earlier)

    def test_the_maker_cap_is_what_forbids_this_trajectory(self):
        """The enforcement position's cumulative value at a live world grows
        linearly, so no constant cap `U` holds: a market maker meeting its
        contract cannot display this price path."""
        gains = [L.compatible_world(h).cumulative_value(ONE)
                 for h in (4, 8, 16, 32)]
        self.assertEqual(gains, [Fraction(1, 2), Fraction(1), Fraction(2),
                                 Fraction(4)])


class ProgressInequality(unittest.TestCase):
    """`E_nu[d] - E_nu[e(w)] = V_N(w) / W_N` exactly on an all-excluded
    trajectory, which is the whole Progress/liability sandwich in one line."""

    def _check(self, traj, world):
        left = traj.size_weighted(traj.defects()) \
            - traj.size_weighted(traj.misfits(world))
        right = traj.cumulative_value(world) / traj.total_size()
        self.assertEqual(left, right)

    def test_on_the_decaying_depth_trajectory(self):
        for horizon in (4, 8, 16):
            self._check(L.decaying_depth(horizon), ONE)

    def test_on_the_fixed_depth_trajectory(self):
        for horizon in (4, 8, 16):
            self._check(L.fixed_depth(horizon), ONE)

    def test_the_signed_identity_holds_at_every_world_of_every_fixture(self):
        """With the *signed* misfit the identity needs no exclusion hypothesis,
        which is why the two account inequalities are stated in it."""
        for traj in (L.decaying_depth(8), L.fixed_depth(8), L.alternating_norm(8),
                     L.compatible_world(6)):
            for world in traj.worlds:
                left = traj.size_weighted(traj.defects()) \
                    - traj.size_weighted(traj.signed_misfits(world))
                right = traj.cumulative_value(world) / traj.total_size()
                self.assertEqual(left, right)

    def test_the_clipped_identity_fails_at_an_admitted_world(self):
        traj = L.compatible_world(6)
        clipped = traj.size_weighted(traj.defects()) \
            - traj.size_weighted(traj.misfits(ONE))
        signed = traj.size_weighted(traj.defects()) \
            - traj.size_weighted(traj.signed_misfits(ONE))
        right = traj.cumulative_value(ONE) / traj.total_size()
        self.assertEqual(signed, right)
        self.assertNotEqual(clipped, right)
        self.assertLess(clipped, right)

    def test_a_bounded_account_forces_the_defect_down_to_the_misfit(self):
        """With `|V_N| <= C`, the service-weighted defect and the
        service-weighted misfit differ by at most `C / W_N`."""
        for horizon in (4, 16, 64):
            traj = L.decaying_depth(horizon)
            gap = traj.size_weighted(traj.defects()) \
                - traj.size_weighted(traj.misfits(ONE))
            self.assertLessEqual(abs(gap),
                                 Fraction(1, 4) / traj.total_size())


if __name__ == "__main__":
    unittest.main()
