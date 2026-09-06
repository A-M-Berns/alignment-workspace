import unittest
from fractions import Fraction as Q

from src.amendment import (bound_holds, quote_reading_target, regret, sealed_target,
                           self_referential_gap)

MENU = ("retain", "provisional", "delegate")


class Amendment(unittest.TestCase):
    def test_argmax_transfer_on_a_finite_menu(self):
        vplus = {"retain": Q(1, 2), "provisional": Q(4, 5), "delegate": Q(3, 5)}
        w = {"retain": Q(1, 2), "provisional": Q(3, 4), "delegate": Q(13, 20)}   # zeta = 1/20
        b = {"retain": Q(11, 20), "provisional": Q(7, 10), "delegate": Q(7, 10)}  # delta = 1/20
        pi = {"provisional": Q(1, 2), "delegate": Q(1, 2)}                       # eta = 0
        self.assertTrue(bound_holds(pi, b, w, vplus, Q(1, 20), Q(1, 20), Q(0)))
        self.assertEqual(regret(pi, vplus), Q(1, 10))
        self.assertLessEqual(regret(pi, vplus), Q(1, 5))

    def test_quote_reading_target_forces_half_gap(self):
        """CM-SR: against a target that reads the quote, no quote is within 1/2, so any
        correspondence radius zeta < 1/2 is unsatisfiable and the bound is vacuous."""
        grid = [Q(k, 1000) for k in range(1001)]
        self.assertEqual(self_referential_gap(grid), Q(1, 2))
        self.assertEqual(quote_reading_target(Q(1, 2)), Q(1))

    def test_sealed_arm_restores_a_fixed_target(self):
        """A target settled by an arm blind to the quote is a fixed vector; a quote
        equal to it is calibrated at radius 0."""
        vplus_sealed = Q(7, 10)
        for b in (Q(0), Q(1, 2), Q(7, 10), Q(1)):
            self.assertEqual(sealed_target(vplus_sealed, b), vplus_sealed)
        self.assertEqual(abs(sealed_target(vplus_sealed, vplus_sealed) - vplus_sealed), Q(0))


if __name__ == "__main__":
    unittest.main()
