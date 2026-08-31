"""Exact checks for Joint Actionability and its countermodels."""
from fractions import Fraction
import unittest

import joint as J
import transfer as T


class ChainInterference(unittest.TestCase):
    """Two reasons, individually actionable, whose regions intersect. The
    per-reason gain of the aggregated move, read against that reason's own
    region, goes strictly negative; the aggregate gain against the common region
    stays above the claimed floor."""

    def setUp(self):
        self.margin = Fraction(1, 4)
        self.reasons = J.chain_reasons(self.margin)
        self.weights = [Fraction(1), Fraction(1)]

    def test_each_reason_is_individually_actionable(self):
        for r in self.reasons:
            self.assertTrue(r.individually_actionable())
        tight = self.reasons[0]
        self.assertEqual(J.gain(tight.move, tight.region, tight.base),
                         tight.margin * tight.defect)

    def test_the_regions_are_jointly_satisfiable(self):
        self.assertFalse(J.common_region(self.reasons).is_empty())

    def test_own_region_gain_of_the_joint_move_is_negative(self):
        joint = J.scaled_sum([r.move for r in self.reasons], self.weights)
        self.assertEqual(joint, [Fraction(-1, 2), Fraction(0), Fraction(1, 2)])
        got = J.own_region_gain(self.reasons[0], joint)
        self.assertEqual(got, Fraction(-1, 8))
        self.assertLess(got, self.margin * self.reasons[0].defect)

    def test_sequential_composition_destroys_it_the_same_way(self):
        net = J.compose([r.move for r in self.reasons])
        self.assertEqual(J.own_region_gain(self.reasons[0], net),
                         Fraction(-1, 8))

    def test_aggregate_gain_against_the_common_region_meets_the_floor(self):
        got = J.aggregate_gain(self.reasons, self.weights)
        self.assertEqual(got, Fraction(1, 2))
        self.assertEqual(J.aggregate_floor(self.reasons, self.weights),
                         Fraction(1, 4))
        self.assertGreaterEqual(got, J.aggregate_floor(self.reasons, self.weights))

    def test_the_floor_holds_at_every_scaling_of_the_intervention(self):
        for a in (Fraction(0), Fraction(1, 3), Fraction(1, 2), Fraction(1)):
            for b in (Fraction(0), Fraction(1, 5), Fraction(3, 4), Fraction(1)):
                weights = [a, b]
                self.assertGreaterEqual(J.aggregate_gain(self.reasons, weights),
                                        J.aggregate_floor(self.reasons, weights))


class EmptyCommonRegion(unittest.TestCase):
    """Conflicting demands: the aggregate move is zero and the common region is
    empty, so the theorem's conclusion is unavailable rather than false."""

    def setUp(self):
        self.reasons = J.conflicting_reasons()

    def test_each_reason_is_individually_actionable(self):
        for r in self.reasons:
            self.assertTrue(r.individually_actionable())

    def test_the_common_region_is_empty(self):
        self.assertTrue(J.common_region(self.reasons).is_empty())
        self.assertIsNone(J.aggregate_gain(self.reasons, [Fraction(1)] * 2))

    def test_the_superposed_move_is_exactly_zero(self):
        joint = J.scaled_sum([r.move for r in self.reasons], [Fraction(1)] * 2)
        self.assertEqual(joint, [Fraction(0), Fraction(0)])
        for r in self.reasons:
            self.assertEqual(J.own_region_gain(r, joint), Fraction(0))
            self.assertLess(Fraction(0), r.margin * r.defect)


class VanishingShare(unittest.TestCase):
    """Aggregate Uptake controls a share-weighted sum. A reason whose share of
    total service vanishes keeps defect density 1 while the aggregate density
    goes to zero."""

    def test_aggregate_density_vanishes_while_the_reason_stays_defective(self):
        aggregate = []
        for horizon in (16, 64, 256, 1024):
            f = J.vanishing_share(horizon)
            total = (sum(f["service_1"], Fraction(0))
                     + sum(f["service_2"], Fraction(0)))
            weighted = sum((w * d for w, d in zip(f["service_2"],
                                                  f["defect_2"])), Fraction(0))
            aggregate.append(weighted / total)
            own = T.normalize(f["service_2"])
            self.assertEqual(T.expectation(own, f["defect_2"]), Fraction(1))
        for earlier, later in zip(aggregate, aggregate[1:]):
            self.assertLess(later, earlier)

    def test_the_starved_reason_is_still_served_without_bound(self):
        totals = []
        for horizon in (16, 64, 256, 1024):
            f = J.vanishing_share(horizon)
            totals.append(sum(f["service_2"], Fraction(0)))
        for earlier, later in zip(totals, totals[1:]):
            self.assertGreater(later, earlier)
        self.assertGreater(totals[-1], Fraction(6))


if __name__ == "__main__":
    unittest.main()
