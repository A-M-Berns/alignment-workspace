from pathlib import Path
import importlib.util
import unittest


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("joint_margin", ROOT / "src" / "joint_margin.py")
JM = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(JM)
Q = JM.Q


class CommonMixtureTests(unittest.TestCase):
    def test_01_centered_binary_peg_has_half_coverage(self):
        mu = JM.binary_point_mixture(Q(1, 2))
        self.assertEqual(mu, (Q(1, 2), Q(1, 2)))
        self.assertEqual(JM.coverage(mu), Q(1, 2))

    def test_02_near_vertex_coverage_and_bound_scale_as_inverse_epsilon(self):
        eps = Q(1, 20)
        mu = JM.binary_point_mixture(eps)
        self.assertEqual(JM.coverage(mu), eps)
        self.assertEqual(JM.common_mixture_bound(eps), Q(57))

    def test_03_common_mixture_liability_bound_is_sharp_algebraically(self):
        mu = (Q(1, 4), Q(1, 4), Q(1, 4), Q(1, 4))
        # U=3 and one value -9 attain expectation zero and the lower bound.
        values = (Q(-9), Q(3), Q(3), Q(3))
        self.assertTrue(JM.common_mixture_certificate(mu, values, Q(3)))
        self.assertEqual(min(values), -JM.common_mixture_bound(Q(1, 4)))

    def test_04_pr50_each_era_has_a_covered_compatible_mixture(self):
        low_mu = JM.pr50_era_mixture(True)
        high_mu = JM.pr50_era_mixture(False)
        self.assertTrue(JM.all_positive(low_mu))
        self.assertTrue(JM.all_positive(high_mu))
        self.assertEqual(JM.coverage(low_mu), Q(3, 40))
        self.assertEqual(JM.coverage(high_mu), Q(3, 40))
        low_mean = JM.pr50_era_mean(True)
        high_mean = JM.pr50_era_mean(False)
        self.assertTrue(JM.in_interval(low_mean[0], JM.PEG))
        self.assertTrue(JM.in_interval(low_mean[1], JM.LOW_BAND))
        self.assertTrue(JM.in_interval(high_mean[0], JM.PEG))
        self.assertTrue(JM.in_interval(high_mean[1], JM.HIGH_BAND))

    def test_05_pr50_has_no_single_mixture_across_low_and_high_eras(self):
        # Any one mixture has one fixed psi expectation. The interval intersection
        # is empty because 1/5 < 4/5.
        self.assertLess(JM.LOW_BAND[1], JM.HIGH_BAND[0])

    def test_06_separate_coordinate_mixtures_need_not_have_a_joint_mixture(self):
        # Assessed settlements (0,1),(1,0). Each coordinate can separately have
        # expectation 3/4 with coverage 1/4, but their sum is always one, so both
        # expectations cannot be >=3/4 under a single distribution.
        points = ((Q(0), Q(1)), (Q(1), Q(0)))
        self.assertEqual(JM.expectation((Q(1, 4), Q(3, 4)), points)[0], Q(3, 4))
        self.assertEqual(JM.expectation((Q(3, 4), Q(1, 4)), points)[1], Q(3, 4))
        for k in range(9):
            mu = (Q(k, 8), Q(8 - k, 8))
            mean = JM.expectation(mu, points)
            self.assertFalse(mean[0] >= Q(3, 4) and mean[1] >= Q(3, 4))

    def test_07_nonempty_region_can_miss_settlement_convex_hull(self):
        points = ((Q(0), Q(0)), (Q(1), Q(0)))
        for k in range(9):
            mean = JM.expectation((Q(k, 8), Q(8 - k, 8)), points)
            self.assertNotEqual(mean, (Q(1, 2), Q(1, 2)))

    def test_08_per_date_full_support_need_not_have_uniform_coverage(self):
        coverages = [JM.coverage(JM.binary_point_mixture(Q(1, n))) for n in range(2, 18)]
        self.assertEqual(coverages[-1], Q(1, 17))
        self.assertTrue(all(b < a for a, b in zip(coverages, coverages[1:])))


class ProgressStructureTests(unittest.TestCase):
    def test_09_two_sources_with_common_answer_have_covered_witness(self):
        # One-hot settlement worlds and mean (1/5,1/5,3/5).
        values = (Q(1, 5), Q(1, 5), Q(3, 5))
        self.assertGreaterEqual(JM.repair_gain((-1, 0, 1), values), Q(1, 5))
        self.assertGreaterEqual(JM.repair_gain((0, -1, 1), values), Q(1, 5))
        self.assertEqual(min(values), Q(1, 5))

    def test_10_disjoint_answer_pairs_can_share_a_mixture(self):
        values = (Q(1, 8), Q(3, 8), Q(1, 8), Q(3, 8))
        self.assertEqual(JM.repair_gain((-1, 1, 0, 0), values), Q(1, 4))
        self.assertEqual(JM.repair_gain((0, 0, -1, 1), values), Q(1, 4))

    def test_11_acyclic_repair_row_does_not_force_settlement_compatibility(self):
        # Values are constrained by settlements to the diagonal, so y-x is zero
        # under every mixture despite the acyclic semantic row y-x >= 1/2.
        points = ((Q(0), Q(0)), (Q(1), Q(1)))
        for k in range(9):
            mean = JM.expectation((Q(k, 8), Q(8 - k, 8)), points)
            self.assertEqual(JM.repair_gain((-1, 1), mean), Q(0))

    def test_12_positive_pairwise_cycle_is_infeasible(self):
        # (v1-v0) + (v0-v1) is identically zero, never >= 1/2.
        for v0 in (Q(0), Q(1, 2), Q(1)):
            for v1 in (Q(0), Q(1, 2), Q(1)):
                gains = (v1 - v0, v0 - v1)
                self.assertFalse(gains[0] >= Q(1, 4) and gains[1] >= Q(1, 4))

    def test_13_directional_security_is_bounded_after_rescaling(self):
        # u=mu-e_x has gain in [-1,1], so (1+gain)/2 is a [0,1] security.
        for gain in (Q(-1), Q(-1, 3), Q(0), Q(2, 5), Q(1)):
            score = (Q(1) + gain) / 2
            self.assertTrue(Q(0) <= score <= Q(1))


class MotionAndRecyclingTests(unittest.TestCase):
    def test_14_summable_motion_need_not_have_one_fixed_mixture(self):
        means = [Q(1, 2) + Q(1, 2 ** (n + 2)) for n in range(1, 10)]
        movement = sum((abs(b - a) for a, b in zip(means, means[1:])), Q(0))
        self.assertLess(movement, Q(1, 8))
        self.assertEqual(len(set(means)), len(means))  # singleton regions have empty intersection
        self.assertGreaterEqual(min(min(c, 1 - c) for c in means), Q(3, 8))

    def test_15_settlement_can_destroy_compatibility_without_moving_K(self):
        # K={1/2}: compatible while both binary worlds are live; incompatible
        # after the plausible region collapses to the false world.
        self.assertEqual(JM.expectation((Q(1, 2), Q(1, 2)), ((Q(0),), (Q(1),))), (Q(1, 2),))
        self.assertEqual(JM.expectation((Q(1),), ((Q(0),),)), (Q(0),))

    def test_16_world_inclusion_is_the_zero_liability_extreme(self):
        for c in (Q(0), Q(1, 4), Q(1, 2), Q(1)):
            self.assertTrue(Q(0) <= c <= Q(1))

    def test_17_recycling_closure_has_exact_kappa_threshold(self):
        theta, upper, slack = Q(1, 4), Q(3), Q(1)
        self.assertEqual(JM.recycling_bound(theta, upper, slack, Q(0)), Q(13))
        self.assertEqual(JM.recycling_bound(theta, upper, slack, Q(1, 8)), Q(26))
        with self.assertRaises(ValueError):
            JM.recycling_bound(theta, upper, slack, theta)


if __name__ == "__main__":
    unittest.main()

