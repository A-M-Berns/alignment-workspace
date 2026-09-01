"""Exact checks for row-indexed accounting, capacity, and scheduling."""
from fractions import Fraction
import unittest

import reasonwise as R


class AggregateSafetyDoesNotBoundAReasonBook(unittest.TestCase):
    """One book earns without bound while another loses without bound, and the
    aggregate is identically zero. Both aggregate conditions hold and no
    reason-level ceiling does."""

    def _pair(self, horizon):
        first = R.Book([Fraction(1)] * horizon)
        second = R.Book([Fraction(-1)] * horizon)
        return first, second

    def test_the_aggregate_is_capped_and_floored_at_zero(self):
        for horizon in (4, 16, 64):
            first, second = self._pair(horizon)
            total = R.aggregate([first, second])
            self.assertEqual(total.ceiling(), Fraction(0))
            self.assertEqual(total.floor(), Fraction(0))

    def test_the_first_book_is_unbounded_above(self):
        tops = [self._pair(h)[0].ceiling() for h in (4, 16, 64)]
        self.assertEqual(tops, [Fraction(4), Fraction(16), Fraction(64)])

    def test_the_second_book_is_unbounded_below(self):
        floors = [self._pair(h)[1].floor() for h in (4, 16, 64)]
        self.assertEqual(floors, [Fraction(4), Fraction(16), Fraction(64)])

    def test_the_subset_bound_is_vacuous_without_a_complementary_floor(self):
        """Lemma R1's bound is `U + sum of the complement's floors`, and here
        that complement floor is exactly what diverges."""
        for horizon in (4, 16, 64):
            books = list(self._pair(horizon))
            bound = R.subset_ceiling_bound(books, [0], Fraction(0))
            self.assertEqual(bound, Fraction(horizon))
            self.assertEqual(books[0].ceiling(), bound)


class SubsetCapFromComplementaryFloors(unittest.TestCase):
    """With every other book floored, one book's ceiling is bounded by the
    aggregate cap plus the total of the other floors — uniformly in the subset."""

    def _books(self, horizon):
        # Three rows: two with geometrically bounded losses, one that earns.
        earn = R.Book([Fraction(1, 2 ** t) for t in range(horizon)])
        lose_a = R.Book([Fraction(-1, 4 ** (t + 1)) for t in range(horizon)])
        lose_b = R.Book([Fraction(-1, 8 ** (t + 1)) for t in range(horizon)])
        return [earn, lose_a, lose_b]

    def test_every_subset_obeys_the_uniform_bound(self):
        horizon = 12
        books = self._books(horizon)
        total_floor = sum((b.floor() for b in books), Fraction(0))
        cap = R.aggregate(books).ceiling()
        for subset in ([0], [1], [2], [0, 1], [1, 2], [0, 2]):
            sub = R.aggregate([books[j] for j in subset])
            self.assertLessEqual(sub.ceiling(), cap + total_floor)

    def test_the_complementary_floors_are_summable(self):
        floors = [b.floor() for b in self._books(64)]
        self.assertEqual(floors[0], Fraction(0))
        self.assertLess(sum(floors, Fraction(0)), Fraction(1, 2))


class LocalCapsAreNotLifetimeSafety(unittest.TestCase):
    """Respecting a per-date authority cap at every date says nothing about the
    lifetime account when the allowances are not summable."""

    def test_nonsummable_allowances_drive_the_account_down_without_bound(self):
        for horizon in (8, 32, 128):
            # Every date spends its full allowance of 1; each is inside its own
            # local cap and the cumulative loss is exactly the horizon.
            book = R.Book([Fraction(-1)] * horizon)
            self.assertEqual(book.floor(), Fraction(horizon))

    def test_summable_allowances_do_bound_it(self):
        for horizon in (8, 32, 128):
            book = R.Book([-Fraction(1, 2 ** (t + 1)) for t in range(horizon)])
            self.assertLess(book.floor(), Fraction(1))

    def test_the_cap_is_the_inverse_of_the_charge(self):
        budget, depth = Fraction(3), Fraction(1, 5)
        for allowance in (Fraction(1), Fraction(1, 2), Fraction(7, 3)):
            alloc = R.authority_cap(allowance, budget, depth)
            self.assertEqual(R.charge_squared(alloc, budget, depth),
                             allowance ** 2)


class SignedAccountBeatsPerDateBudgeting(unittest.TestCase):
    """A date on which the account earns enlarges the next date's viable
    authority beyond anything an exogenous summable split allows."""

    def setUp(self):
        self.budget = Fraction(1)
        self.depth = Fraction(1, 2)
        self.total = Fraction(1)          # lifetime liability budget B = 1

    def test_route_a_splits_the_budget_in_advance(self):
        half = self.total / 2
        cap = R.authority_cap(half, self.budget, self.depth)
        self.assertEqual(cap, Fraction(1))

    def test_route_b_spends_the_realized_slack(self):
        # Date one earns 1/4 (the row was violated and the world admitted it),
        # so date two's slack is 1 + 1/4 rather than 1/2.
        earned = Fraction(1, 4)
        slack = self.total + earned
        cap = R.authority_cap(slack, self.budget, self.depth)
        self.assertEqual(cap, Fraction(25, 4))
        self.assertGreater(cap, R.authority_cap(self.total / 2, self.budget,
                                                self.depth))

    def test_the_gap_is_quadratic_in_the_slack(self):
        conservative = R.authority_cap(self.total / 2, self.budget, self.depth)
        adaptive = R.authority_cap(self.total + Fraction(1, 4), self.budget,
                                   self.depth)
        self.assertEqual(adaptive / conservative, Fraction(25, 4))


class ConcentrationBeatsSplitting(unittest.TestCase):
    """Authority is quadratic in the allowance, so time-sharing the allowance
    dominates dividing it — the per-date capacity region is not convex."""

    def setUp(self):
        self.budget = Fraction(1)
        self.depth = Fraction(1, 2)
        self.allowance = Fraction(1)
        self.reasons = 4

    def _totals(self, allowances, horizon):
        depths = [self.depth] * self.reasons
        schedule = R.schedule_from_allowances(allowances, self.budget, depths)
        return R.totals(schedule), R.spend(allowances)

    def test_both_schedules_spend_the_same_allowance_every_date(self):
        horizon = 12
        for allowances in (R.proportional_allowances(horizon, self.reasons,
                                                     self.allowance),
                           R.round_robin_allowances(horizon, self.reasons,
                                                    self.allowance)):
            self.assertEqual(R.spend(allowances), [self.allowance] * horizon)

    def test_round_robin_gives_each_reason_more_authority(self):
        horizon = 12
        prop, _ = self._totals(R.proportional_allowances(
            horizon, self.reasons, self.allowance), horizon)
        rr, _ = self._totals(R.round_robin_allowances(
            horizon, self.reasons, self.allowance), horizon)
        # Proportional: 12 dates at (1/4)^2/(1*(1/2)^2) = 1/4 each.
        self.assertEqual(prop, [Fraction(3)] * 4)
        # Round robin: 3 turns at 1/(1*(1/4)) = 4 each.
        self.assertEqual(rr, [Fraction(12)] * 4)
        for p, r in zip(prop, rr):
            self.assertEqual(r / p, Fraction(self.reasons))

    def test_the_per_date_region_is_not_convex(self):
        """`(1,0)` and `(0,1)` cost allowance 1 each; their midpoint costs more
        than 1, so the set of allocations affordable at allowance 1 is not
        closed under midpoints."""
        depth = Fraction(1, 2)
        budget = Fraction(1)
        corner = R.authority_cap(Fraction(1), budget, depth)
        self.assertEqual(corner, Fraction(4))
        # Midpoint of (4, 0) and (0, 4) is (2, 2); each coordinate costs
        # sqrt(2 * 1) * 1/2, so the squared per-row charge is 1/2 and the two
        # charges sum to sqrt(1/2) + sqrt(1/2) = sqrt(2) > 1.
        each = R.charge_squared(Fraction(2), budget, depth)
        self.assertEqual(each, Fraction(1, 2))
        self.assertGreater(4 * each, Fraction(1))     # (2*sqrt(1/2))^2 = 2 > 1


class DivergentServiceOnAFiniteBudget(unittest.TestCase):
    """Many persistent reasons, a summable lifetime allowance, and every
    reason's allocated service still diverging."""

    def test_every_reason_diverges_under_round_robin(self):
        reasons = 3
        budget = Fraction(1)
        totals = []
        for horizon in (30, 120, 480):
            allowances = []
            for t in range(horizon):
                row = [Fraction(0)] * reasons
                row[t % reasons] = Fraction(1, (t + 1) ** 2)
                allowances.append(row)
            depths = [Fraction(1, 4 ** 1)] * reasons
            # Depth shrinks with the date, which is what makes the cap grow.
            schedule = []
            for t, row in enumerate(allowances):
                depth = Fraction(1, 4 ** (t + 1))
                schedule.append([R.authority_cap(b, budget, depth)
                                 if b > 0 else Fraction(0) for b in row])
            del depths
            self.assertLess(sum(R.spend(allowances), Fraction(0)), Fraction(2))
            totals.append(R.totals(schedule))
        for earlier, later in zip(totals, totals[1:]):
            for a, b in zip(earlier, later):
                self.assertGreater(b, a)
        for value in totals[-1]:
            self.assertGreater(value, Fraction(10 ** 12))


if __name__ == "__main__":
    unittest.main()
