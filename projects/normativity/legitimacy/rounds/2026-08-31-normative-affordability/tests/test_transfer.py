"""Exact checks for the Service Transfer results and their countermodels."""
from fractions import Fraction
import unittest

import transfer as T


class SurfaceFairnessIsNotServiceFidelity(unittest.TestCase):
    """Bounded-deficit Surface Fairness leaves the claim-weighted defect at 1/2.

    This is the countermodel to reading the merged Progress conclusion
    `D_N / W_N -> 0` as a statement about what was owed.
    """

    def test_service_weighted_defect_is_exactly_zero(self):
        for horizon in range(2, 40, 2):
            f = T.rotation(horizon)
            nu = T.normalize(f["service"])
            self.assertEqual(T.expectation(nu, f["defect"]), Fraction(0))

    def test_claim_weighted_defect_is_exactly_one_half(self):
        for horizon in range(2, 40, 2):
            f = T.rotation(horizon)
            mu = T.normalize(f["claims"])
            self.assertEqual(T.expectation(mu, f["defect"]), Fraction(1, 2))

    def test_surface_fairness_deficit_bound_holds_with_eta_one_half(self):
        for horizon in range(2, 40, 2):
            f = T.rotation(horizon)
            served = sum(f["service"], Fraction(0))
            attention = sum(f["claims"], Fraction(0))
            self.assertGreaterEqual(served, Fraction(1, 2) * attention)

    def test_density_is_unbounded_so_contiguity_fails(self):
        f = T.rotation(20)
        mu = T.normalize(f["claims"])
        nu = T.normalize(f["service"])
        self.assertIsNone(T.density_bound(mu, nu))

    def test_the_level_set_is_the_witness_the_proof_uses(self):
        f = T.rotation(20)
        mu = T.normalize(f["claims"])
        nu = T.normalize(f["service"])
        bad = T.level_set(f["defect"], Fraction(1, 2))
        self.assertEqual(T.mass(nu, bad), Fraction(0))
        self.assertEqual(T.mass(mu, bad), Fraction(1, 2))


class ExposureOnEveryDateTransfers(unittest.TestCase):
    """The one Persistent Relevance interface that does give a bounded density."""

    def test_bounded_density_gives_a_quantitative_transfer(self):
        horizon = 24
        claims = [Fraction(1)] * horizon
        service = [Fraction(1, 3)] * horizon      # c_* = 1/3 on every date
        defect = [Fraction(1, 5) if t % 3 else Fraction(0) for t in range(horizon)]
        mu = T.normalize(claims)
        nu = T.normalize(service)
        self.assertEqual(T.density_bound(mu, nu), Fraction(1))
        self.assertEqual(T.transfer_bound(mu, nu, defect),
                         T.expectation(mu, defect))


class DilutionAttack(unittest.TestCase):
    """Padding service onto defect-free dates drives `E_nu[d]` to zero while the
    claim-weighted defect stays at 1. Blocked by the service-to-claim cap."""

    def test_service_weighted_defect_vanishes(self):
        values = []
        for horizon in (10, 20, 40, 80):
            f = T.dilution(horizon)
            nu = T.normalize(f["service"])
            values.append(T.expectation(nu, f["defect"]))
        self.assertEqual(values[0], Fraction(1, 11))
        for earlier, later in zip(values, values[1:]):
            self.assertLess(later, earlier)

    def test_claim_weighted_defect_is_exactly_one(self):
        for horizon in (10, 20, 40, 80):
            f = T.dilution(horizon)
            mu = T.normalize(f["claims"])
            self.assertEqual(T.expectation(mu, f["defect"]), Fraction(1))

    def test_the_service_to_claim_ratio_diverges(self):
        ratios = []
        for horizon in (10, 20, 40, 80):
            f = T.dilution(horizon)
            ratios.append(sum(f["service"], Fraction(0))
                          / sum(f["claims"], Fraction(0)))
        for earlier, later in zip(ratios, ratios[1:]):
            self.assertGreater(later, earlier)


class ArrayVersusFixedDefect(unittest.TestCase):
    """`mu_N = delta_{N-1}`, `nu_N = delta_{N-2}` separates the two versions."""

    def test_a_moving_array_defeats_the_pair(self):
        for horizon in range(3, 30):
            f = T.delay_pair(horizon)
            mu = T.normalize(f["claims"])
            nu = T.normalize(f["service"])
            d = T.moving_defect_array(horizon)
            self.assertEqual(T.expectation(nu, d), Fraction(0))
            self.assertEqual(T.expectation(mu, d), Fraction(1))

    def test_every_fixed_defect_sequence_transfers(self):
        tail = lambda t: Fraction(1, t + 1)
        for horizon in range(3, 40):
            f = T.delay_pair(horizon)
            mu = T.normalize(f["claims"])
            nu = T.normalize(f["service"])
            d = T.fixed_defect(horizon, tail)
            # E_mu[d] = d_{N-1} and E_nu[d] = d_{N-2}: one is the other's
            # successor, so one vanishes exactly when the other does.
            self.assertEqual(T.expectation(mu, d), tail(horizon - 1))
            self.assertEqual(T.expectation(nu, d), tail(horizon - 2))
            self.assertLess(T.expectation(mu, d), T.expectation(nu, d))


class DeferredTransfer(unittest.TestCase):
    """Rotation is repaired by a transport plan exactly when the defect is
    stable across the rotation step."""

    def _plan(self, horizon):
        # Every odd claim date is serviced at the preceding even date.
        rows = {}
        for t in range(horizon):
            rows[(t, t if t % 2 == 0 else t - 1)] = Fraction(1)
        return T.TransportPlan(rows)

    def test_the_plan_is_feasible_and_leaves_no_residual(self):
        horizon = 20
        f = T.rotation(horizon)
        plan = self._plan(horizon)
        self.assertTrue(plan.feasible([Fraction(2)] * horizon))
        self.assertEqual(plan.residual(f["claims"]), Fraction(0))

    def test_an_unstable_defect_makes_the_transport_error_exactly_one(self):
        horizon = 20
        f = T.rotation(horizon)
        plan = self._plan(horizon)
        self.assertEqual(plan.stability_defect(f["defect"], Fraction(1)),
                         Fraction(1))

    def test_a_stable_defect_transfers_with_the_declared_constants(self):
        horizon = 20
        # Defect constant across each rotation block: stability holds with L = 1
        # and eps = 0, and the service-to-claim ratio is capped at 1.
        claims = [Fraction(1)] * horizon
        service = [Fraction(2) if t % 2 == 0 else Fraction(0)
                   for t in range(horizon)]
        defect = [Fraction(1, 4) if (t // 2) % 3 == 0 else Fraction(0)
                  for t in range(horizon)]
        plan = self._plan(horizon)
        self.assertEqual(plan.stability_defect(defect, Fraction(1)), Fraction(0))
        bound = T.deferred_transfer_bound(claims, service, defect, plan,
                                          Fraction(1), Fraction(1))
        mu = T.normalize(claims)
        self.assertLessEqual(T.expectation(mu, defect), bound)

    def test_the_cap_is_load_bearing(self):
        horizon = 20
        f = T.dilution(horizon)
        rows = {(t, t): f["claims"][t] for t in range(horizon)
                if f["claims"][t] > 0}
        plan = T.TransportPlan(rows)
        with self.assertRaises(ValueError):
            T.deferred_transfer_bound(f["claims"], f["service"], f["defect"],
                                      plan, Fraction(1), Fraction(2))


if __name__ == "__main__":
    unittest.main()
