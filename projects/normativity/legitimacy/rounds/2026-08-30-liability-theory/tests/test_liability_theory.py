from fractions import Fraction as F
import unittest

from liability_theory import (
    combined_row_deficit,
    controlled_tv_bound,
    dot,
    max_trimmed_expectation,
    running_liability,
    switching_debt,
    terminal_liability,
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

    def test_terminal_liability_cannot_bound_earlier_range(self):
        e0 = (F(-10), F(1))
        e1 = (F(10), F(-1))
        final = tuple(x+y for x, y in zip(e0, e1))
        self.assertGreaterEqual(dot((F(1, 20), F(19, 20)), e0), 0)
        self.assertGreaterEqual(dot((F(1, 2), F(1, 2)), e1), 0)
        self.assertEqual(terminal_liability(final), 0)
        self.assertGreater(max(e0)-min(e0), F(1) + terminal_liability(final))
        self.assertEqual(max(e0)-min(e0), F(1) + running_liability((e0, final)))

    def test_large_selector_motion_with_zero_inventory_has_zero_debt(self):
        self.assertEqual(
            switching_debt((F(1), F(0)), (F(0), F(1)), (F(0), F(0))), 0
        )

    def test_small_motion_can_have_large_inventory_sensitive_debt(self):
        eps, magnitude = F(1, 100), F(10000)
        old = (F(1, 2), F(1, 2))
        new = (F(1, 2) + eps, F(1, 2) - eps)
        self.assertEqual(total_variation(old, new), eps)
        self.assertEqual(switching_debt(old, new, (-magnitude, F(0))), F(100))

    def test_same_barycenter_can_make_tv_proxy_strict(self):
        # Profiles 0, 1, 2: these mixtures both have barycenter one.
        old = (F(1, 2), F(0), F(1, 2))
        new = (F(0), F(1), F(0))
        profiles = (F(0), F(1), F(2))
        self.assertEqual(dot(old, profiles), dot(new, profiles))
        self.assertEqual(total_variation(old, new), 1)
        linear_inventory = tuple(F(7) * x - F(3) for x in profiles)
        self.assertEqual(switching_debt(old, new, linear_inventory), 0)

    def test_many_monotone_tiny_switches_equal_one_large_tv_switch(self):
        path = tuple((F(1) - F(i, 10), F(i, 10)) for i in range(11))
        tiny_total = sum(
            (total_variation(path[i-1], path[i]) for i in range(1, len(path))), F(0)
        )
        self.assertEqual(tiny_total, total_variation(path[0], path[-1]))

    def test_high_dimension_forces_small_uniform_coverage(self):
        for profile_count in (2, 4, 16):
            theta = F(1, profile_count)
            self.assertEqual(sum((theta for _ in range(profile_count)), F(0)), 1)


if __name__ == "__main__":
    unittest.main()
