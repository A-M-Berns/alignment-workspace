"""Support-based live worlds, and the expectation/worldwise gap."""
from __future__ import annotations

import unittest
from fractions import Fraction as F

from deduction import support_rows
from enforcement import EnforcementTrader, Region, Row, grid
from market import Fragment, cube_vertices, holdings_value, max_gain
from semantics import (compatible, compatible_vertices, credal_nesting,
                       dirac_live, expected_value, price_of, support_bridge_bound,
                       support_capacity, support_live)

BOOLEAN = [(F(0),), (F(1),)]          #: `A` false, `A` true


def midpoint() -> Region:
    return Region(1, [Row([F(1)], F(1, 2)), Row([F(-1)], F(-1, 2))])


def at_most_half() -> Region:
    return Region(1, [Row([F(-1)], F(-1, 2))])


def pinned_false() -> Region:
    return Region(1, [Row([F(1)], F(0)), Row([F(-1)], F(0))])


class TheDiracReadingIsWrong(unittest.TestCase):
    """The canonical regression for the semantic distinction."""

    def test_the_midpoint_constraint_has_no_dirac_admissible_world(self):
        self.assertEqual(dirac_live(BOOLEAN, midpoint()), [])

    def test_both_worlds_are_support_live(self):
        self.assertEqual(support_live(BOOLEAN, midpoint()), BOOLEAN)

    def test_the_witnessing_credence_is_exhibited(self):
        mu = [F(1, 2), F(1, 2)]
        self.assertTrue(compatible(mu, BOOLEAN, midpoint()))
        self.assertEqual(price_of(mu, BOOLEAN), (F(1, 2),))
        self.assertTrue(all(m > 0 for m in mu))

    def test_the_capacities_are_exact(self):
        self.assertEqual([support_capacity(BOOLEAN, midpoint(), i)
                          for i in range(2)], [F(1, 2), F(1, 2)])


class TheLaunderingWitnessDoesNotLaunder(unittest.TestCase):
    """Recomputed under the correct semantics: the world stays live."""

    def test_the_true_world_remains_live(self):
        region = at_most_half()
        self.assertEqual(support_capacity(BOOLEAN, region, 1), F(1, 2))
        self.assertIn((F(1),), support_live(BOOLEAN, region))

    def test_the_dirac_reading_dropped_it(self):
        self.assertEqual(dirac_live(BOOLEAN, at_most_half()), [(F(0),)])

    def test_the_enforcement_position_loses_at_a_live_world(self):
        region = at_most_half()
        trader = EnforcementTrader(region, F(10))
        price = (F(11, 20),)
        position = trader.coefficients(price)
        self.assertEqual(holdings_value(position, price, (F(1),)), F(-9, 40))

    def test_liability_is_therefore_not_automatically_zero(self):
        region = at_most_half()
        trader = EnforcementTrader(region, F(10))
        price = (F(11, 20),)
        worst = min(holdings_value(trader.coefficients(price), price, w)
                    for w in support_live(BOOLEAN, region))
        self.assertLess(worst, 0)


class ExpectationIsNotWorldwise(unittest.TestCase):
    """Where the withdrawn proof of automatic zero liability failed."""

    def setUp(self):
        self.region = at_most_half()
        self.trader = EnforcementTrader(self.region, F(10))
        self.price = (F(11, 20),)
        self.position = self.trader.coefficients(self.price)

    def test_every_admitted_credence_gives_nonnegative_expectation(self):
        for weights in range(0, 21):
            mu = [F(20 - weights, 20), F(weights, 20)]
            if compatible(mu, BOOLEAN, self.region):
                self.assertGreaterEqual(
                    expected_value(self.position, self.price, mu, BOOLEAN), 0, mu)

    def test_but_a_live_world_has_negative_value(self):
        self.assertEqual(
            holdings_value(self.position, self.price, (F(1),)), F(-9, 40))

    def test_the_two_are_related_by_the_pricing_map(self):
        """`E_μ[X]` is the position's value at `π(μ)`, which is why a bound at
        region points is a bound on expectations and nothing more."""
        mu = [F(1, 2), F(1, 2)]
        self.assertEqual(
            expected_value(self.position, self.price, mu, BOOLEAN),
            holdings_value(self.position, self.price, price_of(mu, BOOLEAN)))


class SmallSupportHidesLargeLoss(unittest.TestCase):
    """Expectation control coexists with a large worldwise loss when the support
    capacity is small — which is what a quantitative condition has to exclude."""

    def region(self, cap):
        return Region(1, [Row([F(-1)], -cap)])          # p(A) <= cap

    def test_capacity_matches_the_bound(self):
        for cap in (F(1, 4), F(1, 20), F(1, 100)):
            self.assertEqual(support_capacity(BOOLEAN, self.region(cap), 1), cap)

    def test_the_loss_grows_as_the_capacity_shrinks(self):
        losses = []
        for cap in (F(1, 4), F(1, 20), F(1, 100)):
            region = self.region(cap)
            trader = EnforcementTrader(region, F(4))
            price = (cap + F(1, 4),)
            position = trader.coefficients(price)
            self.assertGreaterEqual(
                expected_value(position, price,
                               [F(1) - cap, cap], BOOLEAN), 0)
            losses.append(holdings_value(position, price, (F(1),)))
        self.assertTrue(all(x < 0 for x in losses))
        self.assertLess(losses[1], losses[0])
        self.assertLess(losses[2], losses[1])


class TheSupportBridge(unittest.TestCase):
    """`X(ω) >= (a - (1-θ)U)/θ`, with `U` named rather than smuggled."""

    def test_the_bound_holds_at_every_live_world(self):
        region = at_most_half()
        trader = EnforcementTrader(region, F(10))
        for price in grid(1, 20):
            position = trader.coefficients(price)
            for index, world in enumerate(BOOLEAN):
                capacity = support_capacity(BOOLEAN, region, index)
                if capacity <= 0:
                    continue
                self.assertGreaterEqual(
                    holdings_value(position, price, world),
                    support_bridge_bound(position, price, capacity),
                    (price, world))

    def test_the_upper_bound_is_the_cube_maximum_gain(self):
        region = at_most_half()
        trader = EnforcementTrader(region, F(10))
        price = (F(11, 20),)
        position = trader.coefficients(price)
        self.assertEqual(max_gain(position, price), F(11, 40))
        self.assertEqual(support_bridge_bound(position, price, F(1, 2)),
                         F(-11, 40))

    def test_it_degrades_as_the_capacity_shrinks(self):
        position, price = (F(-1, 2),), (F(1, 2),)
        bounds = [support_bridge_bound(position, price, cap)
                  for cap in (F(1, 2), F(1, 10), F(1, 100))]
        self.assertLess(bounds[1], bounds[0])
        self.assertLess(bounds[2], bounds[1])

    def test_it_refuses_a_dead_world(self):
        with self.assertRaises(ValueError):
            support_bridge_bound((F(1),), (F(1, 2),), F(0))


class GenuineRemoval(unittest.TestCase):
    """Support vanishing entirely is a different thing from small support."""

    def test_a_pinning_constraint_removes_a_world(self):
        region = pinned_false()
        self.assertEqual(support_capacity(BOOLEAN, region, 1), F(0))
        self.assertEqual(support_live(BOOLEAN, region), [(F(0),)])

    def test_small_support_is_not_removal(self):
        region = Region(1, [Row([F(-1)], F(-1, 1000))])
        self.assertEqual(support_capacity(BOOLEAN, region, 1), F(1, 1000))
        self.assertIn((F(1),), support_live(BOOLEAN, region))


class DeductiveRecoveryUnderSupport(unittest.TestCase):
    """Both directions, on a fragment with a relation."""

    FRAGMENT = Fragment(("phi", "notphi", "psi"), [lambda w: w[0] + w[1] == 1])
    STAGES = ({}, {"phi": 1}, {"phi": 0}, {"phi": 1, "psi": 1})

    def test_live_worlds_equal_the_plausible_worlds(self):
        for settled in self.STAGES:
            worlds = self.FRAGMENT.worlds()
            region = Region(3, support_rows(self.FRAGMENT, settled))
            live = support_live(worlds, region)
            self.assertEqual(sorted(live),
                             sorted(self.FRAGMENT.pc_worlds(settled)), settled)

    def test_forward_direction_uses_the_dirac_credence(self):
        """A plausible world's point mass is compatible, so it is live."""
        settled = {"phi": 1}
        worlds = self.FRAGMENT.worlds()
        region = Region(3, support_rows(self.FRAGMENT, settled))
        for target in self.FRAGMENT.pc_worlds(settled):
            mu = [F(1) if w == target else F(0) for w in worlds]
            self.assertTrue(compatible(mu, worlds, region), target)

    def test_reverse_direction_removes_the_implausible_worlds(self):
        settled = {"phi": 1}
        worlds = self.FRAGMENT.worlds()
        region = Region(3, support_rows(self.FRAGMENT, settled))
        implausible = [w for w in worlds
                       if w not in self.FRAGMENT.pc_worlds(settled)]
        self.assertTrue(implausible)
        for index, world in enumerate(worlds):
            if world in implausible:
                self.assertEqual(support_capacity(worlds, region, index), F(0),
                                 world)


class Nesting(unittest.TestCase):
    """`C_{t+1} ⊆ C_t` implies the live sets nest; revision need not."""

    def test_shrinking_credal_sets_shrink_the_live_set(self):
        earlier, later = at_most_half(), pinned_false()
        self.assertTrue(credal_nesting(BOOLEAN, earlier, later, 24))
        self.assertTrue(set(support_live(BOOLEAN, later))
                        <= set(support_live(BOOLEAN, earlier)))

    def test_an_enlarging_revision_breaks_nesting(self):
        earlier, later = pinned_false(), at_most_half()
        self.assertFalse(credal_nesting(BOOLEAN, earlier, later, 24))
        self.assertFalse(set(support_live(BOOLEAN, later))
                         <= set(support_live(BOOLEAN, earlier)))

    def test_accumulating_settlement_nests(self):
        fragment = DeductiveRecoveryUnderSupport.FRAGMENT
        worlds = fragment.worlds()
        stages = [{}, {"phi": 1}, {"phi": 1, "psi": 1}]
        regions = [Region(3, support_rows(fragment, s)) for s in stages]
        for earlier, later in zip(regions, regions[1:]):
            self.assertTrue(set(support_live(worlds, later))
                            <= set(support_live(worlds, earlier)))


class LiftHypotheses(unittest.TestCase):
    """What a live-world process must supply for the source construction."""

    def test_the_deductive_process_is_nested(self):
        """The budgeter's induction needs a world plausible now to have been
        plausible before."""
        stages = [{}, {"phi": 1}, {"phi": 1, "psi": 1}]
        sets = [set(DeductiveRecoveryUnderSupport.FRAGMENT.pc_worlds(s)) for s in stages]
        for earlier, later in zip(sets, sets[1:]):
            self.assertTrue(later <= earlier)

    def test_each_stage_is_finite_and_nonempty(self):
        for settled in ({}, {"phi": 1}, {"phi": 1, "psi": 1}):
            worlds = DeductiveRecoveryUnderSupport.FRAGMENT.pc_worlds(settled)
            self.assertTrue(worlds)
            self.assertLess(len(worlds), 2 ** 3 + 1)

    def test_an_inconsistent_stage_is_empty_and_must_be_refused(self):
        self.assertEqual(DeductiveRecoveryUnderSupport.FRAGMENT.pc_worlds({"phi": 1, "notphi": 1}), [])

if __name__ == "__main__":
    unittest.main()
