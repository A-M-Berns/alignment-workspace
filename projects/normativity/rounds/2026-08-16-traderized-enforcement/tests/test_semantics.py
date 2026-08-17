"""Semantic credal sets, price projections, and what projection loses."""
from __future__ import annotations

import unittest
from fractions import Fraction as F

from deduction import in_convex_hull, support_rows
from enforcement import EnforcementTrader, Region, Row, grid
from market import Fragment, holdings_value, max_gain
from semantics import (CredalSet, delta_of, dirac_live, expected_value,
                       is_fibre_saturated, preimage_live, price_of,
                       saturated_lift, saturation_witnesses,
                       support_bridge_bound)

#: Two priced sentences, four worlds.
PAIR = [(F(0), F(0)), (F(0), F(1)), (F(1), F(0)), (F(1), F(1))]
#: Deduction admits only the correlated worlds.
CORRELATED = [PAIR[0], PAIR[3]]
#: Their price projection: `{p_A = p_B}`.
DIAGONAL = Region(2, [Row([F(1), F(-1)], F(0)), Row([F(-1), F(1)], F(0))])

BOOLEAN = [(F(0),), (F(1),)]          #: one sentence: `A` false, `A` true


def at_most_half() -> Region:
    return Region(1, [Row([F(-1)], F(-1, 2))])


def midpoint() -> Region:
    return Region(1, [Row([F(1)], F(1, 2)), Row([F(-1)], F(-1, 2))])


class ProjectionLosesSupport(unittest.TestCase):
    """The minimal witness that `π` is not injective on credal sets."""

    def test_the_projection_is_the_diagonal(self):
        semantic = delta_of(PAIR, CORRELATED)
        for world in PAIR:
            self.assertEqual(DIAGONAL.contains(world),
                             in_convex_hull(world, CORRELATED), world)
        for price in semantic.price_vertices():
            self.assertTrue(DIAGONAL.contains(price), price)

    def test_the_anticorrelated_mixture_projects_into_it(self):
        mu = [F(0), F(1, 2), F(1, 2), F(0)]
        self.assertEqual(price_of(mu, PAIR), (F(1, 2), F(1, 2)))
        self.assertTrue(DIAGONAL.contains(price_of(mu, PAIR)))

    def test_but_its_whole_support_is_deductively_impossible(self):
        mu = [F(0), F(1, 2), F(1, 2), F(0)]
        support = [PAIR[i] for i, m in enumerate(mu) if m > 0]
        self.assertEqual(support, [PAIR[1], PAIR[2]])
        for world in support:
            self.assertNotIn(world, CORRELATED)

    def test_the_preimage_reading_returns_every_world(self):
        """Which is why price-space membership does not recover the semantics."""
        self.assertEqual(sorted(preimage_live(PAIR, DIAGONAL)), sorted(PAIR))
        self.assertNotEqual(sorted(preimage_live(PAIR, DIAGONAL)),
                            sorted(CORRELATED))


class SamePriceProjectionDifferentLiveWorlds(unittest.TestCase):
    """Two semantic states a market cannot tell apart."""

    def setUp(self):
        self.tight = delta_of(PAIR, CORRELATED)
        self.loose = saturated_lift(PAIR, DIAGONAL)

    def test_the_projections_agree(self):
        for price in self.tight.price_vertices():
            self.assertTrue(self.loose.projects_to(price), price)
        for price in self.loose.price_vertices():
            self.assertTrue(self.tight.projects_to(price), price)

    def test_the_live_worlds_do_not(self):
        self.assertEqual(self.tight.live_worlds(), CORRELATED)
        self.assertEqual(sorted(self.loose.live_worlds()), sorted(PAIR))

    def test_the_capacities_do_not(self):
        self.assertEqual([self.tight.support_capacity(i) for i in range(4)],
                         [F(1), F(0), F(0), F(1)])
        self.assertEqual([self.loose.support_capacity(i) for i in range(4)],
                         [F(1), F(1, 2), F(1, 2), F(1)])


class FibreSaturation(unittest.TestCase):
    """`C ⊆ π⁻¹(π(C))`, with equality exactly when `C` is saturated."""

    def test_a_deductive_constraint_is_not_saturated(self):
        semantic = delta_of(PAIR, CORRELATED)
        self.assertFalse(is_fibre_saturated(semantic, 4))
        self.assertIn((F(0), F(1, 2), F(1, 2), F(0)),
                      saturation_witnesses(semantic, 2))

    def test_a_price_lift_is_saturated_by_construction(self):
        self.assertTrue(is_fibre_saturated(saturated_lift(PAIR, DIAGONAL), 4))
        self.assertEqual(saturation_witnesses(saturated_lift(PAIR, DIAGONAL), 3),
                         [])

    def test_containment_always_holds(self):
        semantic = delta_of(PAIR, CORRELATED)
        for vertex in semantic.vertices():
            self.assertTrue(semantic.saturation_contains(vertex), vertex)

    def test_separating_worlds_is_not_enough(self):
        """The pricing map is injective on the four *worlds* here and still
        loses the semantic set: separating points is not separating mixtures."""
        images = [price_of([F(1) if k == i else F(0) for k in range(4)], PAIR)
                  for i in range(4)]
        self.assertEqual(len(set(images)), 4)
        self.assertFalse(is_fibre_saturated(delta_of(PAIR, CORRELATED), 4))


class DeductiveSemanticRecovery(unittest.TestCase):
    """`C^D = Δ(PC(D))` gives `Ω^live = PC(D)`, with no hypothesis on `π`."""

    FRAGMENT = Fragment(("phi", "notphi", "psi"), [lambda w: w[0] + w[1] == 1])
    STAGES = ({}, {"phi": 1}, {"phi": 0}, {"phi": 1, "psi": 1})

    def test_recovery_on_the_correlated_pair(self):
        self.assertEqual(delta_of(PAIR, CORRELATED).live_worlds(), CORRELATED)

    def test_recovery_across_stages(self):
        worlds = self.FRAGMENT.worlds()
        for settled in self.STAGES:
            admitted = self.FRAGMENT.pc_worlds(settled)
            self.assertEqual(delta_of(worlds, admitted).live_worlds(),
                             admitted, settled)

    def test_forward_direction_is_the_dirac_credence(self):
        worlds = self.FRAGMENT.worlds()
        admitted = self.FRAGMENT.pc_worlds({"phi": 1})
        semantic = delta_of(worlds, admitted)
        for target in admitted:
            mu = [F(1) if w == target else F(0) for w in worlds]
            self.assertTrue(semantic.contains(mu), target)

    def test_reverse_direction_is_the_definition_of_support(self):
        worlds = self.FRAGMENT.worlds()
        admitted = self.FRAGMENT.pc_worlds({"phi": 1})
        semantic = delta_of(worlds, admitted)
        for index, world in enumerate(worlds):
            if world not in admitted:
                self.assertEqual(semantic.support_capacity(index), F(0), world)

    def test_the_stages_genuinely_differ(self):
        sizes = [len(self.FRAGMENT.pc_worlds(s)) for s in self.STAGES]
        self.assertEqual(sizes, [4, 2, 2, 1])

    def test_the_price_projection_is_the_coherence_polytope(self):
        worlds = self.FRAGMENT.worlds()
        admitted = self.FRAGMENT.pc_worlds({"phi": 1})
        semantic = delta_of(worlds, admitted)
        region = Region(3, support_rows(self.FRAGMENT, {"phi": 1}))
        for price in semantic.price_vertices():
            self.assertTrue(region.contains(price), price)


class CapacityComesFromTheSemanticSet(unittest.TestCase):
    """Computing `θ` from the projection's preimage is a different number."""

    def test_the_two_disagree_on_the_correlated_pair(self):
        self.assertEqual(delta_of(PAIR, CORRELATED).support_capacity(1), F(0))
        self.assertEqual(saturated_lift(PAIR, DIAGONAL).support_capacity(1),
                         F(1, 2))

    def test_a_dead_world_is_dead_in_the_semantic_set(self):
        self.assertNotIn(PAIR[1], delta_of(PAIR, CORRELATED).live_worlds())
        self.assertIn(PAIR[1], saturated_lift(PAIR, DIAGONAL).live_worlds())


class PriceOnlyConstraintsLiftByChoice(unittest.TestCase):
    """When a source supplies only a region, the semantics is a named choice."""

    def test_the_lift_is_saturated(self):
        self.assertTrue(
            is_fibre_saturated(saturated_lift(BOOLEAN, at_most_half()), 8))

    def test_the_midpoint_constraint_keeps_both_worlds_live(self):
        lifted = saturated_lift(BOOLEAN, midpoint())
        self.assertEqual(lifted.live_worlds(), BOOLEAN)
        self.assertEqual([lifted.support_capacity(i) for i in range(2)],
                         [F(1, 2), F(1, 2)])

    def test_the_dirac_reading_would_have_returned_nothing(self):
        self.assertEqual(dirac_live(BOOLEAN, midpoint()), [])

    def test_a_disfavoured_world_stays_live(self):
        lifted = saturated_lift(BOOLEAN, at_most_half())
        self.assertEqual(lifted.support_capacity(1), F(1, 2))
        self.assertIn((F(1),), lifted.live_worlds())


class ExpectationIsNotWorldwise(unittest.TestCase):
    """The distinction the safety story rests on."""

    def setUp(self):
        self.region = at_most_half()
        self.trader = EnforcementTrader(self.region, F(10))
        self.price = (F(11, 20),)
        self.position = self.trader.coefficients(self.price)
        self.lifted = saturated_lift(BOOLEAN, self.region)

    def test_admissible_expectations_are_nonnegative(self):
        for k in range(21):
            mu = [F(20 - k, 20), F(k, 20)]
            if self.lifted.contains(mu):
                self.assertGreaterEqual(
                    expected_value(self.position, self.price, mu, BOOLEAN), 0, mu)

    def test_a_live_world_is_negative(self):
        self.assertEqual(
            holdings_value(self.position, self.price, (F(1),)), F(-9, 40))

    def test_expectation_is_the_value_at_the_projected_price(self):
        mu = [F(1, 2), F(1, 2)]
        self.assertEqual(
            expected_value(self.position, self.price, mu, BOOLEAN),
            holdings_value(self.position, self.price, price_of(mu, BOOLEAN)))


class SupportBridge(unittest.TestCase):
    """One of two sufficient routes from expectations to worldwise bounds."""

    def test_the_bound_holds_at_every_live_world(self):
        region = at_most_half()
        lifted = saturated_lift(BOOLEAN, region)
        trader = EnforcementTrader(region, F(10))
        for price in grid(1, 20):
            position = trader.coefficients(price)
            for index, world in enumerate(BOOLEAN):
                capacity = lifted.support_capacity(index)
                if capacity <= 0:
                    continue
                self.assertGreaterEqual(
                    holdings_value(position, price, world),
                    support_bridge_bound(position, price, capacity),
                    (price, world))

    def test_the_upper_bound_is_named(self):
        region = at_most_half()
        trader = EnforcementTrader(region, F(10))
        price = (F(11, 20),)
        position = trader.coefficients(price)
        self.assertEqual(max_gain(position, price), F(11, 40))
        self.assertEqual(support_bridge_bound(position, price, F(1, 2)),
                         F(-11, 40))

    def test_it_degrades_as_the_capacity_shrinks(self):
        position, price = (F(-1, 2),), (F(1, 2),)
        bounds = [support_bridge_bound(position, price, c)
                  for c in (F(1, 2), F(1, 10), F(1, 100))]
        self.assertLess(bounds[1], bounds[0])
        self.assertLess(bounds[2], bounds[1])

    def test_it_refuses_a_dead_world(self):
        with self.assertRaises(ValueError):
            support_bridge_bound((F(1),), (F(1, 2),), F(0))


class SmallSupportHidesLargeLoss(unittest.TestCase):
    """What a quantitative support condition has to exclude."""

    def region(self, cap):
        return Region(1, [Row([F(-1)], -cap)])

    def test_capacity_matches_the_bound(self):
        for cap in (F(1, 4), F(1, 20), F(1, 100)):
            self.assertEqual(
                saturated_lift(BOOLEAN, self.region(cap)).support_capacity(1), cap)

    def test_the_loss_grows_as_the_capacity_shrinks(self):
        losses = []
        for cap in (F(1, 4), F(1, 20), F(1, 100)):
            region = self.region(cap)
            trader = EnforcementTrader(region, F(4))
            price = (cap + F(1, 4),)
            position = trader.coefficients(price)
            self.assertGreaterEqual(
                expected_value(position, price, [F(1) - cap, cap], BOOLEAN), 0)
            losses.append(holdings_value(position, price, (F(1),)))
        self.assertTrue(all(x < 0 for x in losses))
        self.assertLess(losses[1], losses[0])
        self.assertLess(losses[2], losses[1])


class Nesting(unittest.TestCase):
    """Live-set nesting is what the lift needs; credal nesting implies it."""

    def test_shrinking_credal_sets_shrink_the_live_set(self):
        fragment = DeductiveSemanticRecovery.FRAGMENT
        worlds = fragment.worlds()
        stages = [{}, {"phi": 1}, {"phi": 1, "psi": 1}]
        sets = [delta_of(worlds, fragment.pc_worlds(s)) for s in stages]
        for earlier, later in zip(sets, sets[1:]):
            for vertex in later.vertices():
                self.assertTrue(earlier.contains(vertex), vertex)
            self.assertTrue(set(later.live_worlds()) <= set(earlier.live_worlds()))

    def test_an_enlarging_revision_breaks_it(self):
        tight = delta_of(PAIR, [PAIR[0]])
        loose = delta_of(PAIR, CORRELATED)
        self.assertFalse(set(loose.live_worlds()) <= set(tight.live_worlds()))

    def test_live_set_nesting_is_weaker_than_credal_nesting(self):
        """Two credal sets with the same live worlds and neither contained in the
        other: the lift's hypothesis is about supports, not about the sets."""
        one = CredalSet(BOOLEAN, [([F(1), F(0)], F(1, 4))])     # μ(false) >= 1/4
        two = CredalSet(BOOLEAN, [([F(0), F(1)], F(1, 4))])     # μ(true)  >= 1/4
        self.assertEqual(one.live_worlds(), BOOLEAN)
        self.assertEqual(two.live_worlds(), BOOLEAN)
        self.assertFalse(all(one.contains(v) for v in two.vertices()))
        self.assertFalse(all(two.contains(v) for v in one.vertices()))


class LiftHypotheses(unittest.TestCase):
    """What a live-world process must supply for the source construction."""

    FRAGMENT = DeductiveSemanticRecovery.FRAGMENT

    def test_each_stage_is_finite_and_nonempty(self):
        for settled in ({}, {"phi": 1}, {"phi": 1, "psi": 1}):
            worlds = self.FRAGMENT.pc_worlds(settled)
            self.assertTrue(worlds)
            self.assertLess(len(worlds), 2 ** 3 + 1)

    def test_an_inconsistent_stage_is_empty_and_must_be_refused(self):
        self.assertEqual(self.FRAGMENT.pc_worlds({"phi": 1, "notphi": 1}), [])


if __name__ == "__main__":
    unittest.main()
