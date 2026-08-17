"""A consumer fixture: another component using force through its API alone.

Imports `force_api` and nothing else from this round, which is the point — a
future Normativity component supplying a region should not need the round's
internals to receive a conformance certificate.
"""
from __future__ import annotations

import unittest
from fractions import Fraction as F

from force_api import compile_force


class AConsumerSuppliesRowsAndGetsACertificate(unittest.TestCase):

    def setUp(self):
        # a caller's constraint: p(A) >= 1/2 and p(A) <= 3/4
        self.certificate = compile_force(
            rows=[([F(1)], F(1, 2)), ([F(-1)], F(-3, 4))],
            dimension=1, slack=F(1, 8), volume=F(2), tolerance=F(1, 10))

    def test_the_intensity_follows_the_declaration(self):
        self.assertEqual(self.certificate.intensity, (F(1, 8) + F(2)) / F(1, 100))

    def test_conformance_is_promised_and_checkable(self):
        for numerator in range(0, 41):
            price = (F(numerator, 40),)
            if self.certificate.budget_consumed(price) <= F(1, 8) + F(2):
                self.assertTrue(self.certificate.conformance_holds(price), price)

    def test_a_violating_price_produces_a_position(self):
        price = (F(1, 4),)
        position = self.certificate.position(price)
        self.assertNotEqual(position, (F(0),))
        self.assertGreater(position[0], 0)          # buys, to push the price up

    def test_an_admissible_price_produces_none(self):
        self.assertEqual(self.certificate.position((F(5, 8),)), (F(0),))

    def test_the_liability_ceiling_is_returned_not_discharged(self):
        """Force hands back an obligation; it does not certify safety."""
        self.assertEqual(self.certificate.liability_ceiling((F(0), F(0))), F(0))
        self.assertGreater(self.certificate.liability_ceiling((F(1, 2), F(0))), 0)

    def test_an_empty_region_is_refused(self):
        with self.assertRaises(ValueError):
            compile_force(rows=[([F(1)], F(3, 4)), ([F(-1)], F(-1, 4))],
                          dimension=1, slack=F(1, 8), volume=F(2),
                          tolerance=F(1, 10))


if __name__ == "__main__":
    unittest.main()
