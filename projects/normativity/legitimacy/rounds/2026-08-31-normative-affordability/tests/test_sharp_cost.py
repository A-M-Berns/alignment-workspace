"""Exact checks for the sharp-charge persistence theorem and its neighbours."""
from fractions import Fraction
import unittest

import sharp_cost as S


class TheReviewCounterexample(unittest.TestCase):
    """`s_t = 1/t`, `m_t = t^4`: the conservative friction diverges while the
    sharp charge at a fixed allocation is summable."""

    def test_the_conservative_friction_diverges(self):
        f = S.review_counterexample(8)
        self.assertEqual(f["q"], [Fraction(t) for t in range(1, 9)])

    def test_the_sharp_reference_cost_is_summable(self):
        f = S.review_counterexample(8)
        reference = [c(Fraction(1)) for c in f["costs"]]
        self.assertEqual(reference,
                         [Fraction(1, 4 * t * t) for t in range(1, 9)])
        total = sum(reference, Fraction(0))
        self.assertLess(total, Fraction(1, 2))

    def test_a_constant_allocation_is_sharply_affordable_forever(self):
        for horizon in (8, 64, 256):
            f = S.review_counterexample(horizon)
            alloc = [Fraction(1)] * horizon
            self.assertEqual(S.total_authority(alloc), Fraction(horizon))
            self.assertLess(S.total_charge(f["costs"], alloc), Fraction(1, 2))

    def test_the_allocation_stays_on_the_linear_branch(self):
        f = S.review_counterexample(16)
        for s, m in zip(f["s"], f["m"]):
            self.assertGreaterEqual(S.sharp_branch_point(s, m), Fraction(1))

    def test_so_the_conservative_criterion_is_not_the_sharp_one(self):
        f = S.review_counterexample(64)
        # liminf of the conservative friction is infinite ...
        self.assertGreater(min(f["q"]), Fraction(0))
        # ... while the sharp reference cost tends to zero.
        reference = [c(Fraction(1)) for c in f["costs"]]
        self.assertLess(reference[-1], Fraction(1, 10 ** 4))


class ThePersistenceCriterion(unittest.TestCase):
    """`liminf_t L_t(1) = 0` is sufficient by a geometric tranche construction,
    and necessary because a star-shaped cost charges at least `a L_t(1)` for
    `a <= 1`."""

    def test_dips_give_unbounded_authority_inside_the_budget(self):
        for horizon, gap in ((32, 4), (128, 4), (512, 4)):
            reference = S.sparse_dips(horizon, gap)
            alloc = S.geometric_schedule(reference, Fraction(1))
            charge = sum((r * a for r, a in zip(reference, alloc)), Fraction(0))
            self.assertLessEqual(charge, Fraction(1))
            self.assertGreater(S.total_authority(alloc), Fraction(0))
        totals = [S.total_authority(
            S.geometric_schedule(S.sparse_dips(h, 4), Fraction(1)))
            for h in (32, 128, 512)]
        for earlier, later in zip(totals, totals[1:]):
            self.assertGreater(later, earlier)

    def test_a_floored_reference_cost_caps_the_small_allocations(self):
        """With `L_t(1) >= c`, star-shapedness gives `L_t(a) >= a c` for
        `a <= 1`, so the mass carried by small allocations is at most `B/c`."""
        c, budget = Fraction(1, 4), Fraction(1)
        for horizon in (16, 128, 1024):
            reference = [c] * horizon
            alloc = S.geometric_schedule(reference, budget)
            mass = S.total_authority(alloc)
            self.assertLessEqual(mass, budget / c)

    def test_the_reference_level_does_not_matter(self):
        """`L(1) <= L(lambda) <= lambda L(1)` for `lambda >= 1` by
        star-shapedness, so the criterion is level-independent."""
        s, m = Fraction(1, 3), Fraction(4)
        cost = S.sharp_cost(s, m)
        one = cost(Fraction(1))
        for lam in (Fraction(2), Fraction(5), Fraction(9)):
            self.assertLessEqual(one, cost(lam))
            self.assertLessEqual(cost(lam), lam * one)


class TheFiniteHorizonOptimum(unittest.TestCase):
    """`A_N^max(B) = max_t L_t^{-1}(B)`: a convex objective on a simplex."""

    def test_the_conservative_case_recovers_the_earlier_formula(self):
        q = [Fraction(1), Fraction(1, 3), Fraction(1, 2)]
        budget = Fraction(2)
        inverses = [S.conservative_inverse(qi, budget) for qi in q]
        self.assertEqual(S.horizon_optimum(inverses), Fraction(36))
        self.assertEqual(S.horizon_optimum(inverses),
                         budget ** 2 / min(q) ** 2)

    def test_the_sharp_case_scales_with_the_inverse_square_depth(self):
        m, budget = Fraction(4), Fraction(1)
        for s in (Fraction(1), Fraction(1, 2), Fraction(1, 8)):
            self.assertEqual(S.sharp_inverse(s, m, budget), 4 * budget / s ** 2)

    def test_no_split_beats_the_vertex_under_a_convex_inverse(self):
        """Splitting the budget between two dates and summing `L^{-1}` never
        beats spending it all on the better one."""
        q = [Fraction(1), Fraction(1, 2)]
        budget = Fraction(1)
        best = S.horizon_optimum([S.conservative_inverse(qi, budget)
                                  for qi in q])
        for k in range(0, 9):
            share = Fraction(k, 8)
            split = (S.conservative_inverse(q[0], share)
                     + S.conservative_inverse(q[1], budget - share))
            self.assertLessEqual(split, best)

    def test_an_unbounded_optimum_does_not_imply_persistence(self):
        """`L_t(a) = a` for `a <= 1` and `1 + (a-1)/t` beyond is star-shaped with
        `L_t(1) = 1`, so no dip; yet `L_t^{-1}(2) = 1 + t` is unbounded."""
        def cost(t):
            def inner(a):
                return a if a <= 1 else 1 + (a - 1) / Fraction(t)
            return inner
        for t in (1, 4, 16, 64):
            self.assertEqual(cost(t)(Fraction(1)), Fraction(1))
            self.assertEqual(cost(t)(Fraction(1 + t)), Fraction(2))


class BoundedDelayNeedsSummableWindowMinima(unittest.TestCase):
    """A per-window service floor turns the dip criterion into a summability
    criterion on the window minima."""

    def test_sparse_dips_leave_most_windows_expensive(self):
        reference = S.sparse_dips(64, 16)
        minima = S.window_minima(reference, 4)
        self.assertEqual(len(minima), 16)
        self.assertEqual(sum(1 for x in minima if x == Fraction(1)), 13)

    def test_a_window_floor_is_unaffordable_when_the_minima_are_not_summable(self):
        reference = S.sparse_dips(64, 16)
        minima = S.window_minima(reference, 4)
        floor = Fraction(1)
        charge = sum((m * floor for m in minima), Fraction(0))
        self.assertGreater(charge, Fraction(12))
        # and it grows linearly with the horizon
        bigger = S.window_minima(S.sparse_dips(256, 16), 4)
        self.assertGreater(sum((m * floor for m in bigger), Fraction(0)),
                           Fraction(48))

    def test_summable_window_minima_make_the_floor_affordable(self):
        reference = [Fraction(1, 4 ** (t // 4 + 1)) for t in range(64)]
        minima = S.window_minima(reference, 4)
        charge = sum(minima, Fraction(0))
        self.assertLess(charge, Fraction(1, 2))

    def test_the_unconstrained_criterion_is_strictly_weaker(self):
        """The sparse-dip sequence has `liminf L_t(1) = 0` — so unconstrained
        persistence holds — while its window minima are `1` on a positive
        fraction of windows."""
        reference = S.sparse_dips(256, 16)
        self.assertEqual(min(reference), Fraction(1, 4 ** 15))
        minima = S.window_minima(reference, 4)
        self.assertEqual(sum(1 for x in minima if x == Fraction(1)), 49)


class NoConstantCompetitiveRatio(unittest.TestCase):
    """Two dates already cap any online rule at `1/4`, and a cascade drives the
    achievable ratio to zero."""

    def test_the_two_date_bound_is_one_quarter(self):
        budget = Fraction(1)
        small = Fraction(1, 1000)
        best = Fraction(0)
        for k in range(0, 17):
            commit = Fraction(k, 16)
            stop, cont = S.two_date_ratio(commit, budget, small)
            best = max(best, min(stop, cont))
        self.assertLessEqual(best, Fraction(1, 4))
        stop, cont = S.two_date_ratio(Fraction(1, 2), budget, small)
        self.assertEqual(stop, Fraction(1, 4))
        self.assertLess(cont, Fraction(1, 4) + Fraction(1, 100))

    def test_committing_everything_loses_on_the_continuation(self):
        stop, cont = S.two_date_ratio(Fraction(1), Fraction(1), Fraction(1, 1000))
        self.assertEqual(stop, Fraction(1))
        self.assertEqual(cont, Fraction(1, 10 ** 6))

    def test_committing_nothing_loses_on_the_stop(self):
        stop, cont = S.two_date_ratio(Fraction(0), Fraction(1), Fraction(1, 1000))
        self.assertEqual(stop, Fraction(0))
        self.assertEqual(cont, Fraction(1))

    def test_the_cascade_forces_more_than_the_budget(self):
        """At ratio `1/4` with `delta` small enough, each of `n` stages must
        commit a fixed fraction of the budget, and `n` of them exceed it."""
        budget, ratio = Fraction(1), Fraction(1, 4)
        forced = S.cascade_bound(16, Fraction(1, 1000), budget, ratio)
        self.assertGreater(forced, budget ** 2)


if __name__ == "__main__":
    unittest.main()
