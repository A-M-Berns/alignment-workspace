"""Exact checks for finite-horizon overload certificates."""
from fractions import Fraction
import unittest

import overload as O


def one(n):
    return [Fraction(1)] * n


class CapacityOverload(unittest.TestCase):
    """A single round cannot serve two unit demands: the certificate prices the
    two reasons equally and puts no price on liability."""

    def setUp(self):
        self.program = O.unit_capacity_program(1, 2, Fraction(10), one(2))

    def test_the_certificate_has_a_strictly_positive_deficit(self):
        self.assertEqual(self.program.deficit(one(2), Fraction(0)), Fraction(1))
        self.assertTrue(self.program.certifies_overload(one(2), Fraction(0)))

    def test_no_schedule_meets_the_demand(self):
        for served in ([Fraction(1), Fraction(0)], [Fraction(0), Fraction(1)],
                       [Fraction(1, 2), Fraction(1, 2)]):
            weights = [[Fraction(0), served[0], served[1]]]
            weights[0][0] = 1 - served[0] - served[1]
            self.assertFalse(self.program.admits([served], weights))


class LiabilityOverload(unittest.TestCase):
    """Capacity suffices and the budget does not. The certificate prices
    liability at 1 and both reasons at 1; the deficit is the shortfall."""

    def setUp(self):
        self.program = O.unit_capacity_program(2, 2, Fraction(1), one(2))

    def test_the_certificate_certifies(self):
        self.assertEqual(self.program.deficit(one(2), Fraction(1)), Fraction(1))
        self.assertTrue(self.program.certifies_overload(one(2), Fraction(1)))

    def test_the_capacity_only_certificate_does_not_certify(self):
        self.assertEqual(self.program.deficit(one(2), Fraction(0)), Fraction(0))
        self.assertFalse(self.program.certifies_overload(one(2), Fraction(0)))

    def test_the_trivial_multipliers_certify_nothing(self):
        self.assertEqual(self.program.deficit([Fraction(0)] * 2, Fraction(0)),
                         Fraction(0))
        self.assertFalse(self.program.certifies_overload([Fraction(0)] * 2,
                                                         Fraction(0)))

    def test_the_deficit_grows_with_the_demand(self):
        deficits = []
        for demand in (Fraction(1), Fraction(2), Fraction(5)):
            program = O.unit_capacity_program(8, 2, Fraction(1),
                                              [demand, demand])
            deficits.append(program.deficit(one(2), Fraction(1)))
        self.assertEqual(deficits, [Fraction(1), Fraction(3), Fraction(9)])


class Affordable(unittest.TestCase):
    """Raising the budget to the demand makes the same instance affordable, and
    then no multiplier pair produces a positive deficit."""

    def setUp(self):
        self.program = O.unit_capacity_program(2, 2, Fraction(2), one(2))

    def test_a_primal_witness_is_admitted(self):
        schedule = [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(1)]]
        weights = [[Fraction(0), Fraction(1), Fraction(0)],
                   [Fraction(0), Fraction(0), Fraction(1)]]
        self.assertTrue(self.program.admits(schedule, weights))

    def test_a_grid_of_multipliers_never_certifies(self):
        grid = [Fraction(k, 4) for k in range(0, 13)]
        for y0 in grid:
            for y1 in grid:
                for z in grid:
                    self.assertLessEqual(self.program.deficit([y0, y1], z),
                                         Fraction(0))

    def test_negative_multipliers_are_rejected(self):
        with self.assertRaises(ValueError):
            self.program.deficit([Fraction(-1), Fraction(1)], Fraction(0))


if __name__ == "__main__":
    unittest.main()
