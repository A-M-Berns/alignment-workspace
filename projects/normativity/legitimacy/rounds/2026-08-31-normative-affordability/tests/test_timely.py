"""Exact checks for the ninth pass: eventual service, normalized transport
error, the canonical bound, and deadline insolvency."""
from fractions import Fraction
import unittest

import bounded_delay as BD
import timely as T


ONE = Fraction(1)


class PersistenceGivesEventualFullService(unittest.TestCase):
    """The diagonal assignment serves each claim at its own cheap date. A finite
    prefix of the infinite construction: `k` claims against a horizon carrying
    enough dips to take them one apiece."""

    def _instance(self, claims_count, blocks):
        weights = T.shallow_dip_weights(blocks)
        claims = [ONE] * claims_count + [Fraction(0)] * (len(weights)
                                                         - claims_count)
        return claims, weights

    def test_the_withdrawn_countermodel_admits_a_diagonal_plan(self):
        claims, weights = self._instance(8, 14)
        dates = T.diagonal_assignment(claims, weights, ONE)
        self.assertIsNotNone(dates)
        self.assertEqual(len(dates), 8)
        self.assertLessEqual(T.diagonal_charge(claims, weights, dates), ONE)

    def test_the_service_dates_are_strictly_increasing(self):
        claims, weights = self._instance(8, 14)
        dates = T.diagonal_assignment(claims, weights, ONE)
        for earlier, later in zip(dates, dates[1:]):
            self.assertLess(earlier, later)

    def test_no_claim_is_served_before_it_arrives(self):
        claims, weights = self._instance(8, 14)
        dates = T.diagonal_assignment(claims, weights, ONE)
        positive = [t for t, c in enumerate(claims) if c > 0]
        for t, s in zip(positive, dates):
            self.assertGreaterEqual(s, t)

    def test_more_claims_are_served_as_the_horizon_lengthens(self):
        """Each further dip takes one further claim, which is the finite shadow
        of the infinite diagonal."""
        served = []
        for blocks in (8, 12, 16):
            claims, weights = self._instance(blocks - 6, blocks)
            dates = T.diagonal_assignment(claims, weights, ONE)
            self.assertIsNotNone(dates)
            served.append(len(dates))
        self.assertEqual(served, [2, 6, 10])

    def test_the_block_batching_plan_is_dearer_than_the_diagonal(self):
        """The withdrawn argument priced one plan and read it as the minimum."""
        claims, weights = self._instance(8, 14)
        dates = T.diagonal_assignment(claims, weights, ONE)
        diagonal = T.diagonal_charge(claims, weights, dates)
        # Block batching sends the whole block (2^k, 2^{k+1}] to the dip at
        # 2^{k+1}, at cost 2^k * 2^-(k+1) = 1/2 per block.
        blocks = sum((Fraction(1, 2) for _ in range(8)), Fraction(0))
        self.assertLessEqual(diagonal, ONE)
        self.assertGreater(blocks, diagonal)


class EventualServiceIsNotTimelyService(unittest.TestCase):
    """The one separation that survives: deeper dips, growing gaps."""

    def test_eventual_service_is_affordable(self):
        weights = BD.dip_weights(256, 16)
        claims = [ONE] * 6 + [Fraction(0)] * (len(weights) - 6)
        dates = T.diagonal_assignment(claims, weights, ONE)
        self.assertIsNotNone(dates)
        self.assertLessEqual(T.diagonal_charge(claims, weights, dates), ONE)

    def test_no_fixed_deadline_is(self):
        for delay in (1, 3, 7):
            costs = []
            for horizon in (64, 128, 256):
                weights = BD.dip_weights(horizon, 16)
                claims = [ONE] * (horizon - 16) + [Fraction(0)] * 16
                costs.append(BD.min_cost_linear(claims, weights, delay))
            for earlier, later in zip(costs, costs[1:]):
                self.assertGreater(later, earlier)


class BoundedGapsDoNotSuffice(unittest.TestCase):
    """Cheap dates every other date, friction dipping to zero, and the
    timely-service cost still diverges."""

    def test_the_gaps_are_exactly_two(self):
        weights = T.bounded_gap_weights(8)
        cheap = [t for t, w in enumerate(weights) if w < ONE]
        for earlier, later in zip(cheap, cheap[1:]):
            self.assertEqual(later - earlier, 2)

    def test_the_friction_dips_to_zero(self):
        weights = T.bounded_gap_weights(64)
        self.assertEqual(min(weights), Fraction(1, 64))

    def test_the_timely_service_cost_diverges(self):
        costs = []
        for pairs in (16, 64, 256):
            weights = T.bounded_gap_weights(pairs)
            claims = [ONE] * (len(weights) - 2) + [Fraction(0)] * 2
            costs.append(BD.min_cost_linear(claims, weights, 1))
        for earlier, later in zip(costs, costs[1:]):
            self.assertGreater(later, earlier)
        self.assertGreater(costs[-1], Fraction(10))

    def test_but_eventual_service_is_affordable(self):
        weights = T.bounded_gap_weights(4096)
        claims = [ONE] * 8 + [Fraction(0)] * (len(weights) - 8)
        dates = T.diagonal_assignment(claims, weights, ONE)
        self.assertIsNotNone(dates)
        self.assertLessEqual(T.diagonal_charge(claims, weights, dates), ONE)


class NormalizedTransportError(unittest.TestCase):
    """The transport contribution is an average per unit of claim mass."""

    def setUp(self):
        self.plan = {(0, 0): Fraction(2), (1, 3): ONE, (2, 3): ONE}
        self.claim_mass = Fraction(4)

    def test_the_raw_sum_and_the_average_differ(self):
        modulus = lambda k: Fraction(k)
        error = T.modulus_error(self.plan, modulus)
        raw = sum((m * error[e] for e, m in self.plan.items()), Fraction(0))
        self.assertEqual(raw, Fraction(3))
        self.assertEqual(
            T.normalized_transport_error(self.plan, error, self.claim_mass),
            Fraction(3, 4))

    def test_the_uniform_delay_bound_dominates(self):
        modulus = lambda k: Fraction(k)
        error = T.modulus_error(self.plan, modulus)
        average = T.normalized_transport_error(self.plan, error,
                                               self.claim_mass)
        self.assertLessEqual(average, T.uniform_delay_bound(self.plan,
                                                            modulus, 2))

    def test_a_plan_exceeding_its_declared_delay_is_refused(self):
        modulus = lambda k: Fraction(k)
        with self.assertRaises(ValueError):
            T.uniform_delay_bound(self.plan, modulus, 1)

    def test_a_concave_modulus_gives_a_smaller_average(self):
        square_root_like = lambda k: Fraction(0) if k == 0 else Fraction(1)
        error = T.modulus_error(self.plan, square_root_like)
        self.assertEqual(
            T.normalized_transport_error(self.plan, error, self.claim_mass),
            Fraction(1, 2))


class TheCanonicalBound(unittest.TestCase):
    """`(2 sqrt(B) + sqrt(U)) / sqrt(A_N)`, with the composed claim-weighted
    right-hand side."""

    def test_the_root_is_exact_on_perfect_squares(self):
        self.assertEqual(T.sharp_timely_root(Fraction(1, 4), Fraction(4)),
                         Fraction(3))
        self.assertEqual(T.sharp_timely_root(Fraction(1), Fraction(9)),
                         Fraction(5))

    def test_the_service_weighted_bound(self):
        self.assertEqual(
            T.sharp_timely_bound(Fraction(1, 4), Fraction(4), Fraction(9)),
            ONE)
        self.assertEqual(
            T.sharp_timely_bound(Fraction(1, 4), Fraction(4), Fraction(36)),
            Fraction(1, 2))

    def test_the_bound_vanishes_as_the_allocation_diverges(self):
        values = [T.sharp_timely_bound(Fraction(1, 4), Fraction(4),
                                       Fraction(4 ** k))
                  for k in range(1, 6)]
        for earlier, later in zip(values, values[1:]):
            self.assertLess(later, earlier)
        self.assertEqual(values[-1], Fraction(3, 32))

    def test_the_composed_claim_weighted_bound(self):
        value = T.claim_weighted_bound(
            budget=Fraction(1, 4), ceiling=Fraction(4), allocation=Fraction(9),
            lipschitz=Fraction(2), cap=Fraction(3), transport=Fraction(1, 5),
            defect_bound=ONE, residual_density=Fraction(1, 10))
        self.assertEqual(value, Fraction(6) + Fraction(1, 5) + Fraction(1, 10))

    def test_only_the_transport_term_survives_asymptotically(self):
        transport = Fraction(1, 5)
        values = []
        for k in range(2, 11):
            values.append(T.claim_weighted_bound(
                budget=Fraction(1, 4), ceiling=Fraction(4),
                allocation=Fraction(4 ** k), lipschitz=ONE, cap=ONE,
                transport=transport, defect_bound=ONE,
                residual_density=Fraction(1, 4 ** k)))
        for earlier, later in zip(values, values[1:]):
            self.assertLess(later, earlier)
        self.assertLess(values[-1] - transport, Fraction(1, 100))


class DeadlineInsolvency(unittest.TestCase):
    """A finite certificate: these claims, these remaining legal dates, this
    minimum charge, this slack."""

    def test_the_required_cost_is_the_sliding_window_minimum_from_now(self):
        weights = [ONE, Fraction(1, 2), ONE, Fraction(1, 4)]
        claims = [ONE, ONE, Fraction(0), Fraction(0)]
        self.assertEqual(T.required_cost(claims, weights, 2, 0),
                         Fraction(1, 2) + Fraction(1, 4))

    def test_a_later_now_removes_the_cheap_past(self):
        weights = [Fraction(1, 8), ONE, ONE, ONE]
        claims = [ONE, Fraction(0), Fraction(0), Fraction(0)]
        self.assertEqual(T.required_cost(claims, weights, 3, 0), Fraction(1, 8))
        self.assertEqual(T.required_cost(claims, weights, 3, 1), ONE)

    def test_the_certificate_fires_above_the_slack(self):
        weights = [ONE] * 6
        claims = [ONE] * 4 + [Fraction(0)] * 2
        insolvent, cost = T.deadline_insolvent(claims, weights, 1, 0,
                                               Fraction(3))
        self.assertTrue(insolvent)
        self.assertEqual(cost, Fraction(4))

    def test_it_does_not_fire_inside_the_slack(self):
        weights = [ONE] * 6
        claims = [ONE] * 4 + [Fraction(0)] * 2
        insolvent, cost = T.deadline_insolvent(claims, weights, 1, 0,
                                               Fraction(5))
        self.assertFalse(insolvent)
        self.assertEqual(cost, Fraction(4))

    def test_a_claim_with_no_remaining_legal_date_is_refused(self):
        weights = [ONE] * 6
        claims = [ONE] + [Fraction(0)] * 5
        with self.assertRaises(ValueError):
            T.required_cost(claims, weights, 1, 4)


if __name__ == "__main__":
    unittest.main()
