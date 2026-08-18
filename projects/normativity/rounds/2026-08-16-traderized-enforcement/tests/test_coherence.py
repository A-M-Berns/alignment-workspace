"""The exact dual-distance presentation: rowwise force as an intrinsic measure.

Three things are checked here, in exact rational arithmetic.

**Exactness.** For the deductive coherence polytope `conv(PC(D_t)|_Phi)` the
computed row family's largest violation *equals* the sup-norm distance to the
polytope, at every price on a rational grid. The distance is computed by
enumerating the linear program's basic solutions, which is independent of the
duality the construction rests on, so this is a test rather than a restatement.

**Necessity of the construction.** An arbitrary presentation of the *same* region
gives no distance bound: two near-parallel rows produce a violation-to-distance
ratio of `1/e`, unbounded as the rows close up. Both presentations are
world-inclusive, so the difference is not safety.

**Insufficiency of the net.** The support-function net at a coarse resolution
under-reports, sometimes to zero on a price whose distance is `1/3`. The exact
family reports the distance exactly with fewer rows.
"""
from __future__ import annotations

import unittest
from fractions import Fraction as F
from itertools import product

from coherence import (critical_coefficients, exact_dual_rows, hoffman_ratio,
                       largest_violation, linf_distance_to_hull, support_value)
from deduction import net_rows
from enforcement import Region, Row


def boolean_worlds():
    """`phi`, `psi`, `phi & psi`, `phi | psi` — the four propositionally
    consistent valuations of a fragment closed under both connectives."""
    return [(F(a), F(b), F(min(a, b)), F(max(a, b)))
            for a in (0, 1) for b in (0, 1)]


class TheDistanceProgramIsIndependent(unittest.TestCase):
    """The distance is computed without using the duality under test."""

    def test_a_point_of_the_hull_is_at_distance_zero(self):
        worlds = boolean_worlds()
        for w in worlds:
            self.assertEqual(linf_distance_to_hull(w, worlds), F(0))

    def test_the_midpoint_is_in_the_hull(self):
        worlds = boolean_worlds()
        mid = tuple(sum((w[i] for w in worlds), F(0)) / 4 for i in range(4))
        self.assertEqual(linf_distance_to_hull(mid, worlds), F(0))

    def test_it_recovers_the_settlement_interfaces_number(self):
        """`NL-SI-C5`'s instance, independently of `incoherence_upper`."""
        worlds = [(F(1), F(0), F(0)), (F(1), F(1), F(1)), (F(0), F(1), F(0))]
        self.assertEqual(linf_distance_to_hull((F(9, 10), F(9, 10), F(0)), worlds),
                         F(4, 15))

    def test_a_single_world_gives_the_sup_norm(self):
        self.assertEqual(linf_distance_to_hull((F(1, 2), F(0)), [(F(0), F(0))]),
                         F(1, 2))


class ExactDualDistancePresentation(unittest.TestCase):
    """`max_j g_j(p) == dist_inf(p, conv V)` for every `p`, on two fragments."""

    THREE = [(F(1), F(0), F(0)), (F(1), F(1), F(1)), (F(0), F(1), F(0))]

    def test_three_world_instance_matches_on_the_whole_grid(self):
        rows = exact_dual_rows(self.THREE, 3)
        self.assertEqual(len(rows), 11)
        axis = [F(i, 3) for i in range(4)]
        for p in product(axis, repeat=3):
            self.assertEqual(largest_violation(rows, p),
                             linf_distance_to_hull(p, self.THREE), p)

    def test_it_reports_the_interfaces_number_exactly(self):
        rows = exact_dual_rows(self.THREE, 3)
        self.assertEqual(largest_violation(rows, (F(9, 10), F(9, 10), F(0))),
                         F(4, 15))

    def test_boolean_fragment_matches_on_the_whole_grid(self):
        worlds = boolean_worlds()
        rows = exact_dual_rows(worlds, 4)
        self.assertEqual(len(rows), 17)
        axis = [F(i, 2) for i in range(3)]
        for p in product(axis, repeat=4):
            self.assertEqual(largest_violation(rows, p),
                             linf_distance_to_hull(p, worlds), p)

    def test_every_row_holds_at_every_world(self):
        """World-inclusivity is automatic: each right-hand side is the minimum of
        the row over the worlds. This is why the exact family costs nothing in
        liability — the deductive case keeps `B = 0` however many rows it has."""
        for worlds, dim in ((self.THREE, 3), (boolean_worlds(), 4)):
            region = Region(dim, exact_dual_rows(worlds, dim))
            for w in worlds:
                self.assertTrue(region.contains(w), (w, dim))

    def test_the_rows_are_support_function_rows(self):
        """The exact family is a finite subset of the support-function rows: only
        the right-hand side's origin distinguishes it from a net row."""
        worlds = boolean_worlds()
        for row in exact_dual_rows(worlds, 4):
            self.assertEqual(row.r, support_value(row.c, worlds))

    def test_the_coefficients_are_rational_and_in_the_l1_ball(self):
        worlds = boolean_worlds()
        for c in critical_coefficients(worlds, 4):
            self.assertLessEqual(sum(abs(x) for x in c), F(1))
            for x in c:
                self.assertIsInstance(x, F)

    def test_the_family_does_not_depend_on_the_price(self):
        """`p` enters only the objective, never the feasible region, which is what
        lets the rows be emitted before the market maker chooses a price."""
        worlds = boolean_worlds()
        first = exact_dual_rows(worlds, 4)
        second = exact_dual_rows(worlds, 4)
        self.assertEqual([(r.c, r.r) for r in first], [(r.c, r.r) for r in second])


class ArbitraryPresentationsAreNotIntrinsic(unittest.TestCase):
    """The negative result, parameterized by how near-parallel the rows are.

    `B >= e*A` and `B <= -e*A` cut the origin out of the cube. At `(1/2, 0)` each
    row is violated by `e/2` while the distance is `1/2`, so the ratio is `1/e`.
    """

    PRICE = (F(1, 2), F(0))
    WORLDS = [(F(0), F(0))]

    @staticmethod
    def near_parallel(e):
        return [Row((-e, F(1)), F(0)), Row((-e, F(-1)), F(0))]

    def test_the_ratio_is_one_over_the_angle_parameter(self):
        for e in (F(1, 10), F(1, 100), F(1, 1000)):
            rows = self.near_parallel(e)
            self.assertEqual(largest_violation(rows, self.PRICE), e / 2)
            self.assertEqual(hoffman_ratio(rows, self.PRICE, self.WORLDS), 1 / e)

    def test_the_exact_family_has_ratio_one_at_every_parameter(self):
        rows = exact_dual_rows(self.WORLDS, 2)
        self.assertEqual(hoffman_ratio(rows, self.PRICE, self.WORLDS), F(1))

    def test_both_presentations_cut_out_the_same_region(self):
        """So the ratio is a fact about the presentation and not about `K`."""
        near = Region(2, self.near_parallel(F(1, 100)))
        exact = Region(2, exact_dual_rows(self.WORLDS, 2))
        for point in product([F(i, 4) for i in range(5)], repeat=2):
            self.assertEqual(near.contains(point), exact.contains(point), point)

    def test_both_are_world_inclusive(self):
        for rows in (self.near_parallel(F(1, 100)),
                     exact_dual_rows(self.WORLDS, 2)):
            self.assertEqual(largest_violation(rows, (F(0), F(0))), F(0))


class TheNetIsAnApproximationAndTheExactFamilyIsNot(unittest.TestCase):
    """A coarse net can miss incoherence entirely; the exact family cannot."""

    def test_a_coarse_net_reports_nothing_where_the_distance_is_a_third(self):
        worlds = boolean_worlds()
        price = (F(0), F(0), F(0), F(1))
        self.assertEqual(linf_distance_to_hull(price, worlds), F(1, 3))
        self.assertEqual(largest_violation(net_rows(worlds, 4, 2), price), F(0))
        self.assertEqual(largest_violation(exact_dual_rows(worlds, 4), price),
                         F(1, 3))

    def test_a_finer_net_still_under_reports(self):
        worlds = boolean_worlds()
        price = (F(0), F(0), F(1), F(0))
        self.assertEqual(linf_distance_to_hull(price, worlds), F(1, 2))
        self.assertEqual(largest_violation(net_rows(worlds, 4, 3), price), F(1, 3))
        self.assertEqual(largest_violation(exact_dual_rows(worlds, 4), price),
                         F(1, 2))

    def test_the_exact_family_is_smaller_than_either_net(self):
        worlds = boolean_worlds()
        self.assertEqual(len(exact_dual_rows(worlds, 4)), 17)
        self.assertEqual(len(net_rows(worlds, 4, 2)), 40)
        self.assertEqual(len(net_rows(worlds, 4, 3)), 128)


class TheLipschitzConstantIsOne(unittest.TestCase):
    """The net modulus is `delta + mesh`, not `delta + 2*mesh`, and `1` is
    attained — so the constant cannot be lowered.

    `f_p(c) = min_v <c, v - p>` and `|f_p(c) - f_p(c')| <= ||c - c'||_1` because
    `||v - p||_inf <= 1` on the cube. One world at `0`, price `1`, gives
    `f_p(c) = -c`, so the inequality is an equality.
    """

    def test_the_bound_is_attained(self):
        worlds = [(F(0),)]
        p = (F(1),)
        for c, cp in ((F(1), F(1, 2)), (F(1), F(-1)), (F(1, 4), F(0))):
            fc = support_value((c,), worlds) - c * p[0]
            fcp = support_value((cp,), worlds) - cp * p[0]
            self.assertEqual(abs(fc - fcp), abs(c - cp))

    def test_a_two_mesh_modulus_would_be_slack(self):
        """Recorded as a regression: the sharp constant is `1`, so a modulus
        stated with `2*mesh` is true but not tight, and the round states `1`."""
        worlds = [(F(0),)]
        p = (F(1),)
        c, cp, mesh = F(-1), F(-3, 4), F(1, 4)
        delta = support_value((cp,), worlds) - cp * p[0]
        gap = support_value((c,), worlds) - c * p[0]
        self.assertEqual((delta, gap), (F(3, 4), F(1)))
        self.assertEqual(abs(c - cp), mesh)
        self.assertEqual(gap, delta + mesh)          # attained, so `1` is sharp
        self.assertEqual(gap, linf_distance_to_hull(p, worlds))


if __name__ == "__main__":
    unittest.main()
