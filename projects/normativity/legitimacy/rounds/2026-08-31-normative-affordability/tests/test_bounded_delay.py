"""Exact checks for bounded-delay feasibility, cost, duality and the online gap."""
from fractions import Fraction
import unittest

import bounded_delay as BD
import sharp_cost as S


ONE = Fraction(1)


class IntervalFeasibility(unittest.TestCase):
    """Feasibility against a given service profile is exactly the interval
    condition, and prefixes are not enough."""

    def test_prefixes_pass_while_an_interval_fails(self):
        claims = [Fraction(0), ONE]
        service = [ONE, Fraction(0)]
        # The prefix conditions both hold ...
        self.assertLessEqual(claims[0], service[0])
        self.assertLessEqual(sum(claims, Fraction(0)), sum(service, Fraction(0)))
        # ... and the interval [1,1] fails, because service cannot run backwards.
        self.assertIn((1, 1), BD.interval_condition(claims, service, 0))

    def test_fifo_agrees_with_the_interval_condition(self):
        cases = [
            ([ONE, ONE, ONE], [ONE, ONE, ONE], 0),
            ([ONE, ONE, ONE], [Fraction(0), Fraction(3), Fraction(0)], 1),
            ([ONE, ONE, ONE], [Fraction(0), Fraction(0), Fraction(3)], 1),
            ([Fraction(2), Fraction(0)], [ONE, ONE], 1),
            ([Fraction(2), Fraction(0)], [ONE, ONE], 0),
        ]
        for claims, service, delay in cases:
            feasible = not BD.interval_condition(claims, service, delay)
            self.assertEqual(feasible,
                             not BD.fifo_misses(claims, service, delay),
                             msg=f"{claims} {service} H={delay}")

    def test_a_deferred_batch_is_feasible_at_the_right_delay(self):
        claims = [ONE, ONE, ONE]
        service = [Fraction(0), Fraction(0), Fraction(3)]
        self.assertEqual(BD.interval_condition(claims, service, 2), [])
        self.assertNotEqual(BD.interval_condition(claims, service, 1), [])


class MinimumCostIsTheSlidingWindowMinimum(unittest.TestCase):
    """For linear date costs the optimum is exactly
    `sum_t c_t min_{s in [t, t+H]} w_s`."""

    def test_each_claim_takes_the_cheapest_date_in_its_own_window(self):
        weights = [Fraction(1), Fraction(1, 4), Fraction(1)]
        claims = [ONE, ONE, Fraction(0)]
        self.assertEqual(BD.min_cost_linear(claims, weights, 1),
                         Fraction(1, 4) + Fraction(1, 4))
        self.assertEqual(BD.min_cost_linear(claims, weights, 0),
                         Fraction(1) + Fraction(1, 4))

    def test_the_dp_agrees_with_the_closed_form_on_linear_costs(self):
        weights = BD.dip_weights(24, 4)
        costs = BD.linear_costs(weights)
        claims = [ONE] * 20 + [Fraction(0)] * 4
        for delay in (0, 1, 2, 3, 4):
            self.assertEqual(BD.min_cost_dp(claims, costs, delay),
                             BD.min_cost_linear(claims, weights, delay))

    def test_the_cost_is_nonincreasing_in_the_delay(self):
        weights = BD.dip_weights(32, 4)
        claims = [ONE] * 28 + [Fraction(0)] * 4
        costs = [BD.min_cost_linear(claims, weights, h) for h in range(0, 6)]
        for earlier, later in zip(costs, costs[1:]):
            self.assertLessEqual(later, earlier)

    def test_a_wider_window_reaches_the_dips(self):
        weights = BD.dip_weights(16, 4)
        claims = [ONE] * 12 + [Fraction(0)] * 4
        # At H = 0 every claim pays its own date; at H = 3 every claim can reach
        # the next dip.
        self.assertEqual(BD.min_cost_linear(claims, weights, 0),
                         sum(weights[:12], Fraction(0)))
        self.assertLess(BD.min_cost_linear(claims, weights, 3),
                        BD.min_cost_linear(claims, weights, 0))


class PersistenceWithoutServiceability(unittest.TestCase):
    """A dip sequence satisfies unconstrained persistence and fails bounded-delay
    service, because the dips are spaced wider than the deadline."""

    def test_the_sequence_has_dips(self):
        weights = BD.dip_weights(256, 16)
        self.assertEqual(min(weights), Fraction(1, 4 ** 15))
        self.assertEqual(weights[0], ONE)

    def test_unconstrained_persistence_is_affordable(self):
        weights = BD.dip_weights(256, 16)
        alloc = S.geometric_schedule(weights, ONE)
        charge = sum((w * a for w, a in zip(weights, alloc)), Fraction(0))
        self.assertLessEqual(charge, ONE)
        self.assertGreater(S.total_authority(alloc), Fraction(0))

    def test_bounded_delay_service_is_not(self):
        weights = BD.dip_weights(256, 16)
        claims = [ONE] * 240 + [Fraction(0)] * 16
        # With a deadline of three, most claims never see a dip.
        cost = BD.min_cost_linear(claims, weights, 3)
        self.assertGreater(cost, Fraction(180))

    def test_and_the_cost_grows_linearly_with_the_horizon(self):
        costs = []
        for horizon in (64, 128, 256):
            weights = BD.dip_weights(horizon, 16)
            claims = [ONE] * (horizon - 16) + [Fraction(0)] * 16
            costs.append(BD.min_cost_linear(claims, weights, 3))
        for earlier, later in zip(costs, costs[1:]):
            self.assertGreater(later, earlier)

    def test_a_deadline_matching_the_dip_spacing_restores_it(self):
        weights = BD.dip_weights(64, 4)
        claims = [ONE] * 60 + [Fraction(0)] * 4
        self.assertLess(BD.min_cost_linear(claims, weights, 3), Fraction(4))


class TheCriticalDelay(unittest.TestCase):
    """The affordable delays form an up-set, so a least one exists."""

    def test_the_least_affordable_delay(self):
        weights = BD.dip_weights(64, 4)
        claims = [ONE] * 60 + [Fraction(0)] * 4
        self.assertIsNone(BD.critical_delay(claims, weights, Fraction(1), 2))
        self.assertEqual(BD.critical_delay(claims, weights, Fraction(4), 8), 3)

    def test_a_larger_budget_buys_a_smaller_delay(self):
        weights = BD.dip_weights(64, 4)
        claims = [ONE] * 60 + [Fraction(0)] * 4
        loose = BD.critical_delay(claims, weights, Fraction(4), 8)
        tight = BD.critical_delay(claims, weights, Fraction(70), 8)
        self.assertLess(tight, loose)


class TheDeadlineInsolvencyCertificate(unittest.TestCase):
    """A finite, authenticated certificate: these claims, this neighbourhood,
    this mass, this cost, more than the remaining budget."""

    def test_a_disjoint_interval_packing_certifies_infeasibility(self):
        weights = [ONE] * 12
        costs = BD.linear_costs(weights)
        claims = [ONE] * 12
        # Four separated single-claim intervals, delay 0, so the neighbourhoods
        # are the dates themselves and are disjoint.
        certifies, total = BD.deadline_certificate(
            claims, costs, 0, [(0, 0), (3, 3), (6, 6), (9, 9)], Fraction(3))
        self.assertTrue(certifies)
        self.assertEqual(total, Fraction(4))

    def test_it_does_not_certify_inside_the_budget(self):
        weights = [ONE] * 12
        costs = BD.linear_costs(weights)
        claims = [ONE] * 12
        certifies, total = BD.deadline_certificate(
            claims, costs, 0, [(0, 0), (3, 3)], Fraction(3))
        self.assertFalse(certifies)
        self.assertEqual(total, Fraction(2))

    def test_overlapping_neighbourhoods_are_refused(self):
        weights = [ONE] * 12
        costs = BD.linear_costs(weights)
        claims = [ONE] * 12
        with self.assertRaises(ValueError):
            BD.deadline_certificate(claims, costs, 2, [(0, 0), (1, 1)],
                                    Fraction(1))

    def test_the_certificate_is_sound_against_the_true_optimum(self):
        weights = BD.dip_weights(32, 8)
        costs = BD.linear_costs(weights)
        claims = [ONE] * 24 + [Fraction(0)] * 8
        _, total = BD.deadline_certificate(
            claims, costs, 1, [(0, 0), (4, 4), (8, 8), (12, 12)], Fraction(0))
        self.assertLessEqual(total, BD.min_cost_linear(claims, weights, 1))


class TheOnlineDeadlineGap(unittest.TestCase):
    """Waiting is no longer free, and no competitive ratio survives."""

    def test_committing_early_loses_when_the_second_date_is_cheap(self):
        online, offline = BD.two_date_service(ONE, Fraction(1, 1000), ONE)
        self.assertEqual(online, ONE)
        self.assertEqual(offline, Fraction(1, 1000))
        self.assertEqual(online / offline, Fraction(1000))

    def test_waiting_loses_when_the_second_date_is_expensive(self):
        online, offline = BD.two_date_service(ONE, Fraction(1000), Fraction(0))
        self.assertEqual(online, Fraction(1000))
        self.assertEqual(offline, ONE)
        self.assertEqual(online / offline, Fraction(1000))

    def test_no_commitment_fraction_bounds_both_ratios(self):
        cheap, dear = Fraction(1, 1000), Fraction(1000)
        best = None
        for k in range(0, 11):
            commit = Fraction(k, 10)
            a, b = BD.two_date_service(ONE, cheap, commit)
            c, d = BD.two_date_service(ONE, dear, commit)
            worst = max(a / b, c / d)
            best = worst if best is None else min(best, worst)
        self.assertGreater(best, Fraction(400))

    def test_the_gap_is_absent_when_the_second_date_is_known(self):
        online, offline = BD.two_date_service(ONE, Fraction(1, 4), Fraction(0))
        self.assertEqual(online, offline)


if __name__ == "__main__":
    unittest.main()
