from fractions import Fraction as F
import unittest

from liability_theory import (
    combined_row_deficit,
    controlled_tv_bound,
    dot,
    max_trimmed_expectation,
    switching_debt,
    total_variation,
    underwriting_bound,
)


class UnderwritingTests(unittest.TestCase):
    def test_li_constants(self):
        self.assertEqual(underwriting_bound(F(1, 4), F(3)), F(9))

    def test_binary_point_coverage(self):
        for c in (F(1, 2), F(1, 8), F(7, 8)):
            self.assertEqual(min(c, 1-c), min((1-c, c)))

    def test_abstract_bound_is_sharp(self):
        theta, upper = F(1, 4), F(3)
        loss = underwriting_bound(theta, upper)
        self.assertEqual(dot((theta, 1-theta), (-loss, upper)), 0)

    def test_deficit_version_is_sharp(self):
        theta, upper, deficit = F(1, 3), F(2), F(1, 2)
        loss = underwriting_bound(theta, upper, deficit)
        self.assertEqual(dot((theta, 1-theta), (-loss, upper)), -deficit)

    def test_trimmed_hull_formula(self):
        self.assertEqual(max_trimmed_expectation((F(0), F(1)), F(1, 4)), F(3, 4))

    def test_zero_coverage_is_rejected(self):
        with self.assertRaises(ValueError):
            underwriting_bound(F(0), F(3))


class DualityTests(unittest.TestCase):
    def test_individual_rows_jointly_unsupported(self):
        profiles = ((F(0), F(1)), (F(1), F(0)))
        deficit = combined_row_deficit(
            profiles, (F(3, 4), F(3, 4)), (F(1, 2), F(1, 2)), F(1, 4)
        )
        self.assertEqual(deficit, F(1, 4))

    def test_supported_rows_have_no_positive_witness_here(self):
        profiles = ((F(0), F(1)), (F(1), F(0)))
        deficit = combined_row_deficit(
            profiles, (F(1, 4), F(1, 4)), (F(1, 2), F(1, 2)), F(1, 4)
        )
        self.assertLessEqual(deficit, 0)

    def test_uniform_trim_is_singleton_at_maximum_theta(self):
        self.assertEqual(max_trimmed_expectation((F(2), F(5)), F(1, 2)), F(7, 2))


class DriftTests(unittest.TestCase):
    def test_binary_mean_distance_equals_tv(self):
        c, d = F(1, 5), F(4, 5)
        self.assertEqual(total_variation((1-c, c), (1-d, d)), abs(c-d))

    def test_switching_identity_tight(self):
        mu0, e0 = (F(1, 2), F(1, 2)), (F(-1), F(1))
        mu1, e1 = (F(5, 8), F(3, 8)), (F(3), F(-5))
        self.assertEqual(dot(mu0, e0), 0)
        self.assertEqual(dot(mu1, e1), 0)
        debt = switching_debt(mu0, mu1, e0)
        inventory = tuple(x+y for x, y in zip(e0, e1))
        self.assertEqual(debt, F(1, 4))
        self.assertEqual(dot(mu1, inventory), -debt)

    def test_tv_closure_example(self):
        self.assertEqual(controlled_tv_bound(F(3, 8), F(2), F(1, 8)), F(6))

    def test_tv_threshold_is_strict(self):
        with self.assertRaises(ValueError):
            controlled_tv_bound(F(1, 4), F(2), F(1, 4))

    def test_pairwise_zero_set_gap_does_not_bound_path(self):
        # Selectors for {0}, [0,1], {1} must move by at least one in total.
        for middle in (F(0), F(1, 4), F(1, 2), F(3, 4), F(1)):
            self.assertEqual(abs(middle-F(0)) + abs(F(1)-middle), F(1))

    def test_no_trade_is_bounded_without_common_region(self):
        # Alternating singleton regions have empty intersection, but E=0 is bounded.
        inventory = (F(0), F(0))
        self.assertEqual(max((-x for x in inventory), default=F(0)), 0)

    def test_anti_reset_adds_ledgers(self):
        old, new = (F(-2), F(1)), (F(1), F(-1))
        consolidated = tuple(x+y for x, y in zip(old, new))
        self.assertEqual(consolidated, (F(-1), F(0)))


if __name__ == "__main__":
    unittest.main()

