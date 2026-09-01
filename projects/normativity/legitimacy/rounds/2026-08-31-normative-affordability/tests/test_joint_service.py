"""Exact checks for the joint objective and the batching hypotheses."""
from fractions import Fraction
import unittest

import joint_service as J


ONE = Fraction(1)


class LiabilityIsTheFrictionNumerator(unittest.TestCase):
    """On the sharp charge's linear branch the settlement-friction numerator is
    exactly four times the liability charge."""

    def test_the_identity_holds_termwise(self):
        depths = [Fraction(1, 2), Fraction(1, 3), Fraction(2, 5)]
        alloc = [Fraction(3), Fraction(7, 2), Fraction(1, 4)]
        self.assertEqual(J.friction_numerator(alloc, depths),
                         4 * J.linear_charge(alloc, depths))

    def test_a_budget_bounds_the_numerator_uniformly(self):
        depths = [Fraction(1, k) for k in range(1, 33)]
        alloc = [Fraction(4, 1) for _ in depths]
        budget = J.linear_charge(alloc, depths)
        self.assertEqual(J.friction_numerator(alloc, depths), 4 * budget)

    def test_persistent_service_drives_the_mean_square_to_zero(self):
        """With the charge held at `B` and the allocation diverging, the
        service-weighted mean-square depth is at most `4B / A_N`."""
        budget = ONE
        for blocks in (4, 6, 8):
            # depth 2^-k on the k-th date, allocation chosen to spend a
            # geometric tranche of the budget there.
            depths, alloc = [], []
            for k in range(1, blocks + 1):
                d = Fraction(1, 2 ** k)
                charge = budget / 2 ** k
                alloc.append(4 * charge / d ** 2)
                depths.append(d)
            spent = J.linear_charge(alloc, depths)
            self.assertLessEqual(spent, budget)
            total = sum(alloc, Fraction(0))
            mean_square = J.friction_numerator(alloc, depths) / total
            self.assertLessEqual(mean_square, 4 * budget / total)

    def test_the_allocation_diverges_while_the_charge_is_capped(self):
        budget = ONE
        totals = []
        for blocks in (4, 6, 8, 10):
            alloc = []
            for k in range(1, blocks + 1):
                d = Fraction(1, 2 ** k)
                alloc.append(4 * (budget / 2 ** k) / d ** 2)
            totals.append(sum(alloc, Fraction(0)))
        for earlier, later in zip(totals, totals[1:]):
            self.assertGreater(later, earlier)
        self.assertEqual(totals[-1], Fraction(8184))
        self.assertGreater(totals[-1], Fraction(8000))


class TheBranchIsLoadBearing(unittest.TestCase):
    """The identity is a statement about the linear branch, and the branch point
    is where it stops."""

    def test_the_branch_point_is_reported(self):
        depths = [Fraction(1, 2), Fraction(1, 4)]
        scales = [Fraction(1), Fraction(1, 100)]
        self.assertEqual(J.branch_points(depths, scales),
                         [Fraction(16), Fraction(16, 25)])

    def test_a_small_allocation_stays_on_the_branch(self):
        depths = [Fraction(1, 2), Fraction(1, 4)]
        scales = [Fraction(1), Fraction(1)]
        self.assertTrue(J.on_linear_branch([ONE, ONE], depths, scales))

    def test_a_vanishing_engine_scale_leaves_it(self):
        depths = [ONE, ONE]
        scales = [Fraction(1, 64), Fraction(1, 64)]
        self.assertFalse(J.on_linear_branch([ONE, ONE], depths, scales))


class SplittingCanBeatAtomicAssignment(unittest.TestCase):
    """Star-shaped is not enough for the no-splitting lemma; concavity is."""

    def test_the_cost_is_star_shaped(self):
        cost = J.star_shaped_not_concave()
        previous = None
        for k in range(1, 41):
            a = Fraction(k, 10)
            ratio = cost(a) / a
            if previous is not None:
                self.assertLessEqual(ratio, previous)
            previous = ratio

    def test_the_cost_is_not_concave(self):
        cost = J.star_shaped_not_concave()
        # midpoint of 1 and 3 is 2; concavity would need L(2) >= (L(1)+L(3))/2.
        self.assertLess(cost(Fraction(2)),
                        (cost(ONE) + cost(Fraction(3))) / 2)

    def test_splitting_strictly_wins(self):
        f = J.splitting_beats_atomic()
        self.assertEqual(f["atomic"], Fraction(5, 2))
        self.assertEqual(f["split"], Fraction(2))
        self.assertLess(f["split"], f["atomic"])


class CrossedAssignmentCanBeatMonotone(unittest.TestCase):
    """Concavity is not enough for the run structure; equal claim masses are
    what the exchange needs."""

    def test_both_costs_are_concave(self):
        f = J.crossed_beats_monotone()
        for cost in (f["flat"], f["half"]):
            for k in range(1, 20):
                a, b = Fraction(k), Fraction(k + 2)
                mid = (a + b) / 2
                self.assertGreaterEqual(cost(mid), (cost(a) + cost(b)) / 2)

    def test_the_crossed_assignment_is_cheaper(self):
        f = J.crossed_beats_monotone()
        self.assertEqual(f["crossed"], Fraction(1, 2) + Fraction(11, 10))
        self.assertEqual(f["monotone"], ONE + Fraction(5))
        self.assertLess(f["crossed"], f["monotone"])

    def test_equal_masses_make_the_exchange_free(self):
        """With equal masses the swap leaves both dates' loads unchanged, so it
        cannot change the cost."""
        f = J.crossed_beats_monotone()
        mass = Fraction(3)
        one = f["flat"](mass) + f["half"](mass)
        two = f["half"](mass) + f["flat"](mass)
        self.assertEqual(one, two)


class UniformDelayIsStrongerThanEventualService(unittest.TestCase):
    """Three genuinely different problems, with two strict separations."""

    def test_eventual_full_service_is_affordable(self):
        costs = [J.eventual_service_cost(b) for b in (4, 8, 12, 16)]
        for earlier, later in zip(costs, costs[1:]):
            self.assertGreater(later, earlier)
        self.assertLess(costs[-1], Fraction(1, 2))

    def test_every_fixed_deadline_misses_unboundedly_many_claims(self):
        for delay in (1, 4, 16):
            misses = [J.uniform_delay_misses(b, delay) for b in (8, 10, 12)]
            for earlier, later in zip(misses, misses[1:]):
                self.assertGreater(later, earlier)

    def test_so_the_limit_of_the_bounded_delay_cost_exceeds_the_unbounded_one(self):
        # Each missed claim costs at least 1, so the bounded-delay cost is at
        # least the miss count, which diverges at every fixed deadline; the
        # unbounded-delay cost stays under 1/2.
        self.assertGreater(J.uniform_delay_misses(12, 16), 1000)
        self.assertLess(J.eventual_service_cost(12), Fraction(1, 2))

    def test_persistence_can_hold_where_even_eventual_service_fails(self):
        """Dips too shallow to carry their block: the allocation still diverges
        on a finite budget, and full service does not."""
        costs = [J.shallow_eventual_cost(b) for b in (4, 8, 16)]
        self.assertEqual(costs, [Fraction(2), Fraction(4), Fraction(8)])
        for earlier, later in zip(costs, costs[1:]):
            self.assertGreater(later, earlier)


class TheCombinedScoreHasTwoPrices(unittest.TestCase):
    """On the linear branch the friction weight is four times the liability
    weight, so the three-price score collapses to two."""

    def setUp(self):
        self.depths = [ONE, Fraction(1, 2), Fraction(1, 4), Fraction(1, 8)]
        self.weights = [d ** 2 / 4 for d in self.depths]
        self.frictions = [d ** 2 for d in self.depths]

    def test_the_friction_weight_is_four_times_the_liability_weight(self):
        for w, r in zip(self.weights, self.frictions):
            self.assertEqual(r, 4 * w)

    def test_the_two_prices_collapse_into_one(self):
        for lam in (Fraction(1), Fraction(3)):
            for mu in (Fraction(0), Fraction(1, 2), Fraction(2)):
                for claim in range(2):
                    for date in range(claim, 4):
                        combined = J.combined_score(
                            self.weights, self.frictions, Fraction(1),
                            lam, mu, claim, date)
                        single = J.combined_score(
                            self.weights, self.frictions, Fraction(1),
                            lam + 4 * mu, Fraction(0), claim, date)
                        self.assertEqual(combined, single)

    def test_the_cheapest_liability_date_is_not_always_the_best_date(self):
        """A delay price large enough makes the nearer, dearer date win."""
        cheap = J.best_date(self.weights, self.frictions, Fraction(0),
                            ONE, Fraction(0), 0, 3)
        timely = J.best_date(self.weights, self.frictions, Fraction(1),
                             ONE, Fraction(0), 0, 3)
        self.assertEqual(cheap, 3)
        self.assertEqual(timely, 0)


if __name__ == "__main__":
    unittest.main()
