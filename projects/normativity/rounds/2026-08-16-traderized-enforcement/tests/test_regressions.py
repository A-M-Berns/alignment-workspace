"""Regressions for two claims this round made and withdrew.

Each test here pins a counterexample found in review. They are kept together, and
kept as tests rather than prose, because a withdrawn claim that leaves no
executable trace is one a later pass will make again.
"""
from __future__ import annotations

import unittest
from fractions import Fraction as F

from contract import ForceDeclaration, volume_times_depth
from semantics import dirac_live, preimage_live, saturated_lift
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


class DiracLiveWorldsAreNotLiveWorlds(unittest.TestCase):
    """**Withdrawn:** live worlds are the `{0,1}` worlds whose own price vector
    lies in the admissible region, and therefore a constraint launders its own
    liability by excluding them.

    Both halves fail. A world is live when *some* admitted credence gives it
    positive mass, which does not require its point mass to be admitted. Under
    the Dirac reading `K = {p(A) = 1/2}` has **no** live worlds at all; under the
    correct one both worlds are live at capacity `1/2`. And the laundering witness
    does not launder: under `K = {p(A) <= 1/2}` the true world keeps capacity
    `1/2`, stays live, and the enforcement position still loses there.

    What survives is the distinction the error concealed: the enforcement
    inequality bounds *expectations* under admitted credences, not worldwise
    payoffs.
    """

    WORLDS = [(F(0),), (F(1),)]

    def test_the_dirac_reading_empties_the_midpoint_constraint(self):
        region = Region(1, [Row([F(1)], F(1, 2)), Row([F(-1)], F(-1, 2))])
        self.assertEqual(dirac_live(self.WORLDS, region), [])
        self.assertEqual(preimage_live(self.WORLDS, region), self.WORLDS)

    def test_the_laundering_witness_keeps_its_world(self):
        region = Region(1, [Row([F(-1)], F(-1, 2))])
        self.assertEqual(dirac_live(self.WORLDS, region), [(F(0),)])
        self.assertEqual(
            saturated_lift(self.WORLDS, region).support_capacity(1), F(1, 2))
        self.assertIn((F(1),), preimage_live(self.WORLDS, region))

    def test_the_enforcement_position_still_loses_at_that_world(self):
        region = Region(1, [Row([F(-1)], F(-1, 2))])
        trader = EnforcementTrader(region, F(10))
        price = (F(11, 20),)
        self.assertEqual(
            holdings_value(trader.coefficients(price), price, (F(1),)), F(-9, 40))


class PerRowToleranceNeedsPositiveDisturbance(unittest.TestCase):
    """**Narrowed:** `beta_j >= (eps + M)/delta^2` does not by itself force
    `g_j <= delta`.

    The step is `beta*g^2 <= eps + M <= beta*delta^2`, and dividing by `beta`
    needs `beta > 0`. At `eps + M = 0` the intensity condition is satisfied by
    `beta = 0`, and then the conformance bound `sum_j beta_j g_j^2 <= 0` holds at
    every price, so no row is constrained at all. The Lean statement
    `EnforcementStrategy.rowViolation_le_of_intensity_ge` therefore carries
    `0 < eps + M`, which is automatic in the source market: the market maker's
    slack is `2^-(n+1)` at every date, so the disturbance is never zero.
    """

    def test_at_zero_disturbance_the_intensity_condition_is_empty(self):
        disturbance, tolerance = F(0), F(1, 10)
        self.assertEqual(disturbance / tolerance ** 2, F(0))
        # beta = 0 meets it, and then the weighted square is zero at any price
        for violation in (F(1, 2), F(1), F(3, 4)):
            self.assertLessEqual(F(0) * violation ** 2, disturbance)
            self.assertGreater(violation, tolerance)

    def test_with_positive_disturbance_the_bound_bites(self):
        """The same arithmetic with `eps + M > 0`: the intensity is forced
        positive, and the violation is forced under the tolerance."""
        disturbance, tolerance = F(1, 8), F(1, 10)
        beta = disturbance / tolerance ** 2
        self.assertEqual(beta, F(25, 2))
        self.assertGreater(beta, 0)
        # beta * g^2 <= disturbance and beta * delta^2 = disturbance force g <= delta
        self.assertEqual(beta * tolerance ** 2, disturbance)
        for violation in (F(1, 10), F(1, 20), F(0)):
            self.assertLessEqual(beta * violation ** 2, disturbance)
        for violation in (F(11, 100), F(1, 5)):
            self.assertGreater(beta * violation ** 2, disturbance)


class IntensityIsFixedBeforeThePrice(unittest.TestCase):
    """The intensities are not a response to the violation the maker realises.

    Structural rather than numerical: `certified_intensity` is a function of the
    declared slack, the declared volume bound and the promised tolerance, none of
    which is a price; and the compiled trader carries the same intensities to
    every price it is evaluated at. In the Lean term this is not an argument at
    all -- the intensities are `EF.const` leaves of a term whose arguments are the
    presentation and the date, and the rank bound is what says the coefficients
    read no price later than day `n`.
    """

    REGION = Region(1, [Row((F(1),), F(1, 2))])
    DECLARATION = ForceDeclaration(REGION, volume=F(1, 4), slack=F(1, 8),
                                   tolerance=F(1, 10))

    def test_the_intensity_does_not_take_a_price(self):
        from contract import certified_intensity
        self.assertEqual(self.DECLARATION.intensity,
                         certified_intensity(F(1, 8), F(1, 4), F(1, 10)))

    def test_the_same_intensity_is_carried_to_every_price(self):
        trader = EnforcementTrader(self.REGION, self.DECLARATION.intensity)
        betas = trader.betas
        for price in ((F(0),), (F(1, 4),), (F(1, 2),), (F(1),)):
            trader.coefficients(price)
            self.assertEqual(trader.betas, betas, price)

    def test_a_larger_realised_violation_does_not_raise_it(self):
        trader = EnforcementTrader(self.REGION, self.DECLARATION.intensity)
        small = self.REGION.violations((F(2, 5),))
        large = self.REGION.violations((F(0),))
        self.assertLess(small[0], large[0])
        self.assertEqual(trader.betas, trader.betas)
        # the position scales with the violation; the intensity does not
        self.assertEqual(trader.coefficients((F(0),))[0],
                         trader.betas[0] * large[0])
        self.assertEqual(trader.coefficients((F(2, 5),))[0],
                         trader.betas[0] * small[0])


if __name__ == "__main__":
    unittest.main()
