from fractions import Fraction as Q
import pathlib
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from src.fixtures import (  # noqa: E402
    harmonic_defects,
    opposite_pairwise_rows_feasible,
    power_of_two_applicability,
    restricted_witness_holds,
    row_active,
    weighted_mass,
)


class RestrictedWitnessFixtures(unittest.TestCase):
    def test_pairwise_sensitivity_on_exact_grid(self) -> None:
        grid = [Q(i, 8) for i in range(9)]
        vals = [(x, y) for x in grid for y in grid if y - x >= Q(1, 4)]
        for p in grid:
            self.assertTrue(restricted_witness_holds(p, Q(1, 4), vals))

    def test_inquiry_surface_is_same_mathematics(self) -> None:
        vals = [(Q(0), Q(1, 4)), (Q(1, 2), Q(3, 4))]
        self.assertTrue(restricted_witness_holds(Q(2, 3), Q(1, 4), vals))

    def test_conflicting_strict_pairwise_rows_are_infeasible(self) -> None:
        self.assertFalse(opposite_pairwise_rows_feasible(Q(1, 2), Q(1, 2)))
        self.assertTrue(opposite_pairwise_rows_feasible(Q(0), Q(0)))

    def test_attention_theater_has_zero_relevant_mass(self) -> None:
        W, D = weighted_mass([Q(1)] * 20, [Q(0)] * 20, [Q(1)] * 20)
        self.assertEqual(W, 0)
        self.assertEqual(D, 0)

    def test_sparse_predictable_applicability_can_still_diverge(self) -> None:
        c = power_of_two_applicability(65)
        W, D = weighted_mass([Q(1)] * 65, c, [Q(1, 2)] * 65)
        self.assertEqual(W, 7)  # 1,2,4,8,16,32,64
        self.assertEqual(D, Q(7, 2))

    def test_defect_can_vanish_without_an_answer_event(self) -> None:
        defects = harmonic_defects(64)
        W, D = weighted_mass([Q(1)] * 64, [Q(1)] * 64, defects)
        self.assertEqual(W, 64)
        self.assertLess(D / W, Q(1, 10))

    def test_defeat_disables_without_deleting_occurrence(self) -> None:
        self.assertTrue(row_active(enabled=True, applicable=True, disposed=False))
        self.assertFalse(row_active(enabled=False, applicable=True, disposed=False))
        self.assertFalse(row_active(enabled=True, applicable=True, disposed=True))

    def test_face_only_dominance_is_not_global(self) -> None:
        on_face = [(Q(0), Q(1, 2))]
        with_dissent = on_face + [(Q(1), Q(0))]
        self.assertTrue(restricted_witness_holds(Q(1), Q(1, 2), on_face))
        self.assertFalse(restricted_witness_holds(Q(1), Q(1, 2), with_dissent))

    def test_intermediate_usefulness_has_no_eventual_nonnegative_witness(self) -> None:
        rho0 = [Q(1), Q(-1)] * 8
        rho1 = [Q(-1), Q(1)] * 8
        self.assertEqual(sum(rho0), 0)
        self.assertEqual(sum(rho1), 0)
        self.assertTrue(all(max(a, b) > 0 for a, b in zip(rho0, rho1)))
        self.assertFalse(all(g >= 0 for g in rho0))
        self.assertFalse(all(g >= 0 for g in rho1))


if __name__ == "__main__":
    unittest.main()
