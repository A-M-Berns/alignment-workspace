"""Regressions for two claims this round made and withdrew.

Each test here pins a counterexample found in review. They are kept together, and
kept as tests rather than prose, because a withdrawn claim that leaves no
executable trace is one a later pass will make again.
"""
from __future__ import annotations

import unittest
from fractions import Fraction as F

from contract import ForceDeclaration, volume_times_depth
from deduction import world_deficit
from enforcement import EnforcementTrader, Region, Row, grid
from exactness import min_max_gain, strict_interior_point
from market import holdings_value, max_gain


class IntensityFreeCeilingIsFalse(unittest.TestCase):
    """**Withdrawn:** `L_t(W) <= C_t * max_j d_j(W)`.

    The reasoning was that at equilibrium the enforcement position offsets the
    ordinary one, so its size is the ordinary volume whatever the intensity. That
    holds only where the aggregate is forced to vanish. Positive market-maker
    slack does not force it: the contract bounds the aggregate's cube maximum
    gain, and at an interior price that leaves room for residual enforcement
    demand which nothing cancels. Here the ordinary position is **zero** and the
    enforcement position is thirteen and a half times the declared volume bound.
    """

    REGION = Region(1, [Row([F(-1)], F(-1, 2))])          # K = {P <= 1/2}
    WORLD = (F(1),)
    VOLUME, SLACK, TOLERANCE = F(1, 100), F(1, 8), F(1, 10)
    PRICE = (F(51, 100),)

    def setUp(self):
        self.declaration = ForceDeclaration(self.REGION, self.VOLUME,
                                            self.SLACK, self.TOLERANCE)

    def test_the_declaration_is_the_one_the_rule_prescribes(self):
        self.assertEqual(self.declaration.intensity, F(27, 2))

    def test_the_contract_is_satisfied_with_no_ordinary_position(self):
        position = self.declaration.trader().coefficients(self.PRICE)
        self.assertEqual(self.REGION.rows[0].violation(self.PRICE), F(1, 100))
        self.assertEqual(position, (F(-27, 200),))
        self.assertEqual(max_gain(position, self.PRICE), F(1377, 20000))
        self.assertLessEqual(max_gain(position, self.PRICE), self.SLACK)

    def test_conformance_holds(self):
        self.assertTrue(self.declaration.conformance_holds(self.PRICE))

    def test_the_liability_exceeds_the_withdrawn_ceiling(self):
        position = self.declaration.trader().coefficients(self.PRICE)
        liability = -holdings_value(position, self.PRICE, self.WORLD)
        ceiling = volume_times_depth(self.VOLUME,
                                     world_deficit(self.REGION, self.WORLD))
        self.assertEqual(liability, F(1323, 20000))
        self.assertEqual(ceiling, F(1, 200))
        self.assertGreater(liability, ceiling)

    def test_the_surviving_pointwise_bound_still_holds(self):
        """`sum_j beta_j g_j d_j` is what the kernel-checked identity gives, and
        it survives — tightly."""
        position = self.declaration.trader().coefficients(self.PRICE)
        liability = -holdings_value(position, self.PRICE, self.WORLD)
        self.assertLessEqual(liability,
                             self.declaration.liability_bound(self.PRICE,
                                                              self.WORLD))
        self.assertEqual(self.declaration.liability_bound(self.PRICE,
                                                          self.WORLD), F(27, 400))

    def test_the_surviving_declared_quantity_bound_still_holds(self):
        """`(eps + C) * sum_j d_j / delta`, in which the intensity does not
        cancel and a tighter tolerance makes the bound worse."""
        position = self.declaration.trader().coefficients(self.PRICE)
        liability = -holdings_value(position, self.PRICE, self.WORLD)
        declared = ((self.SLACK + self.VOLUME)
                    * sum(world_deficit(self.REGION, self.WORLD))
                    / self.TOLERANCE)
        self.assertEqual(declared, F(27, 40))
        self.assertLessEqual(liability, declared)


class EmptyInteriorDoesNotImplyImpossibility(unittest.TestCase):
    """**Withdrawn:** exactness is impossible whenever the region has empty
    interior in the cube.

    The proved theorem hypothesises a region strictly inside the open interval,
    which is what forces a sign change and with it a band of cancellable prices.
    A region sitting on a cube face has no such forcing: a position pointing off
    the face costs the disturbance nothing to leave, so a constant trader pins it.
    """

    BUDGET = F(1, 4)

    def strategy(self, coefficient):
        return lambda price: (coefficient,)

    def test_a_vertex_region_at_zero_is_exactly_enforced(self):
        for intensity in (F(1, 2), F(1), F(4)):
            self.assertGreater(intensity, self.BUDGET)
            feasible = [p for p in grid(1, 40)
                        if min_max_gain(self.strategy(-intensity)(p), p,
                                        self.BUDGET) <= 0]
            self.assertEqual(feasible, [(F(0),)])

    def test_a_vertex_region_at_one_is_exactly_enforced(self):
        """Settlement to probability one is the easy case, not the hard one."""
        for intensity in (F(1, 2), F(1), F(4)):
            feasible = [p for p in grid(1, 40)
                        if min_max_gain(self.strategy(intensity)(p), p,
                                        self.BUDGET) <= 0]
            self.assertEqual(feasible, [(F(1),)])

    def test_a_settlement_face_in_two_dimensions_is_exactly_enforced(self):
        feasible = [p for p in grid(2, 8)
                    if min_max_gain((F(1), F(0)), p, self.BUDGET) <= 0]
        self.assertEqual(len(feasible), 9)
        self.assertTrue(all(p[0] == 1 for p in feasible))

    def test_the_proved_theorem_keeps_its_hypothesis(self):
        """A region strictly inside the open interval still has no strict
        interior point and still admits a cancellable band."""
        point = Region(1, [Row([F(1)], F(1, 2)), Row([F(-1)], F(-1, 2))])
        self.assertIsNone(strict_interior_point(point, 24))
        for slope in (F(1), F(10), F(1000)):
            half = self.BUDGET / slope
            self.assertGreater(half, 0)
            escape = (F(1, 2) + half,)
            self.assertFalse(point.contains(escape))
            self.assertLessEqual(
                min_max_gain((slope * (F(1, 2) - escape[0]),), escape,
                             self.BUDGET), 0)


class CoherenceSegmentIsStillHard(unittest.TestCase):
    """The case the withdrawn generalisation got right, isolated from the case
    it got wrong: a coherence relation cuts a segment that meets the open cube,
    so it lies in no proper face and the sign-change obstruction applies."""

    REGION = Region(2, [Row([F(1), F(1)], F(1)), Row([F(-1), F(-1)], F(-1))])
    BUDGET = F(1, 4)

    def test_it_lies_in_no_proper_face(self):
        interior_witness = (F(1, 2), F(1, 2))
        self.assertTrue(self.REGION.contains(interior_witness))
        self.assertTrue(all(F(0) < x < F(1) for x in interior_witness))

    def test_a_cancellable_band_survives_every_intensity(self):
        """Exact rationals: a grid coarser than `C / (2 beta)` reports none."""
        for beta in (F(1), F(10), F(100)):
            trader = EnforcementTrader(self.REGION, beta)
            gap = self.BUDGET / (4 * beta)          # inside the band
            escape = (F(1, 2) + gap, F(1, 2))
            self.assertFalse(self.REGION.contains(escape))
            self.assertLessEqual(
                min_max_gain(trader.coefficients(escape), escape, self.BUDGET),
                0, beta)

    def test_the_grid_would_have_missed_it(self):
        trader = EnforcementTrader(self.REGION, F(100))
        escapes = [p for p in grid(2, 8)
                   if min_max_gain(trader.coefficients(p), p, self.BUDGET) <= 0
                   and not self.REGION.contains(p)]
        self.assertEqual(escapes, [])


if __name__ == "__main__":
    unittest.main()
