"""Deduction as a constraint source, and what enforcement is not."""
from __future__ import annotations

import random
import unittest
from fractions import Fraction as F

from deduction import (coherence_membership, deductive_region,
                       in_convex_hull, liability_identity,
                       persistent_gap_trader_worth, relation_rows,
                       support_rows, world_deficit, world_inclusive)
from enforcement import (EnforcementTrader, Region, Row,
                         contract_feasible_prices, grid)
from market import Fragment, dot, holdings_value, max_gain

#: A fragment closed under the two connectives, so its coherence polytope has
#: facets that no affine relation among the priced sentences supplies.
BOOLEAN = Fragment(("phi", "psi", "and", "or"),
                   [lambda w: w[2] == min(w[0], w[1]),
                    lambda w: w[3] == max(w[0], w[1])])

NEGATION = Fragment(("phi", "notphi"), [lambda w: w[0] + w[1] == 1])


class SupportPresentation(unittest.TestCase):
    """Right-hand sides read off the still-plausible worlds."""

    def test_world_inclusive_by_construction(self):
        for settled in ({}, {"phi": 1}, {"phi": 0}):
            region = Region(4, support_rows(BOOLEAN, settled))
            self.assertTrue(world_inclusive(region,
                                            BOOLEAN.pc_worlds(settled)),
                            settled)

    def test_it_cuts_out_the_coherence_polytope(self):
        region = Region(4, support_rows(BOOLEAN, {}))
        worlds = BOOLEAN.worlds()
        for p in grid(4, 3):
            self.assertEqual(region.contains(p), in_convex_hull(p, worlds), p)

    def test_the_region_is_not_a_point(self):
        """A theorem that only enforces because the region is a singleton would
        hard-code its own answer."""
        region = Region(4, support_rows(BOOLEAN, {}))
        interior = [p for p in grid(4, 2) if region.contains(p)]
        self.assertGreater(len(interior), 5)


class AffineRelationsAreNotEnough(unittest.TestCase):
    """The cheap presentation enforces strictly less than coherence."""

    def test_affine_rows_admit_incoherent_prices(self):
        region = Region(4, relation_rows(BOOLEAN))
        escapes = [p for p in grid(4, 3)
                   if region.contains(p) and not in_convex_hull(p, BOOLEAN.worlds())]
        self.assertEqual(len(escapes), 24)
        self.assertIn((F(0), F(1, 3), F(1, 3), F(0)), escapes)

    def test_the_named_escape_violates_a_real_coherence_row(self):
        """`p(phi and psi) > p(phi)` is priced, and no affine relation says so."""
        p = (F(0), F(1, 3), F(1, 3), F(0))
        self.assertGreater(p[2], p[0])
        self.assertFalse(in_convex_hull(p, BOOLEAN.worlds()))
        region = Region(4, support_rows(BOOLEAN, {}))
        self.assertFalse(region.contains(p))


class TraderizedDeduction(unittest.TestCase):
    """W10 — a stage sequence, enforced onto the coherence polytope."""

    STAGES = {1: {}, 2: {"phi": 1}, 3: {"phi": 1}}

    def test_prices_are_coherent_at_every_date(self):
        for date, settled in self.STAGES.items():
            region = Region(2, support_rows(NEGATION, settled))
            trader = EnforcementTrader(region, F(1))
            feasible = contract_feasible_prices(trader, 6, F(0))
            self.assertTrue(feasible, date)
            for p in feasible:
                self.assertTrue(coherence_membership(p, NEGATION, settled),
                                (date, p))

    def test_a_settled_sentence_is_priced_at_one(self):
        region = Region(2, support_rows(NEGATION, {"phi": 1}))
        trader = EnforcementTrader(region, F(1))
        for p in contract_feasible_prices(trader, 6, F(0)):
            self.assertEqual(p, (F(1), F(0)))

    def test_before_settlement_the_price_is_free(self):
        """Enforcement adds nothing where deduction has said nothing — the
        mechanism is not smuggling in an answer."""
        region = Region(2, support_rows(NEGATION, {}))
        trader = EnforcementTrader(region, F(1))
        feasible = contract_feasible_prices(trader, 4, F(0))
        self.assertEqual(len(feasible), 5)          # the whole segment p0+p1=1

    def test_liability_is_zero_across_the_stage_sequence(self):
        for date, settled in self.STAGES.items():
            region = Region(2, support_rows(NEGATION, settled))
            trader = EnforcementTrader(region, F(3))
            for p in grid(2, 4):
                zeta = trader.coefficients(p)
                for w in NEGATION.pc_worlds(settled):
                    self.assertGreaterEqual(holdings_value(zeta, p, w), 0,
                                            (date, p, w))


class LiabilityIdentity(unittest.TestCase):
    """The exact decomposition the coverage condition is read off."""

    def test_identity_on_random_instances(self):
        random.seed(7)
        for _ in range(2000):
            rows = [Row(tuple(F(random.randint(-2, 2)) for _ in range(3)),
                        F(random.randint(-3, 3), 2)) for _ in range(3)]
            region = Region(3, rows)
            trader = EnforcementTrader(
                region, tuple(F(random.randint(1, 5)) for _ in range(3)))
            p = tuple(F(random.randint(0, 4), 4) for _ in range(3))
            w = tuple(F(random.randint(0, 1)) for _ in range(3))
            self.assertEqual(holdings_value(trader.coefficients(p), p, w),
                             liability_identity(trader, region, p, w))

    def test_both_factors_are_needed_for_a_loss(self):
        """A live violation with no excluded world costs nothing; an excluded
        world with no live violation costs nothing."""
        region = Region(1, [Row([F(-1)], F(-1, 2))])       # p <= 1/2
        trader = EnforcementTrader(region, F(2))
        world = (F(1),)
        self.assertEqual(world_deficit(region, world), (F(1, 2),))
        inside = (F(1, 4),)
        self.assertEqual(region.violations(inside), (F(0),))
        self.assertEqual(holdings_value(trader.coefficients(inside), inside,
                                        world), 0)
        outside = (F(3, 4),)
        self.assertEqual(region.violations(outside), (F(1, 4),))
        self.assertEqual(holdings_value(trader.coefficients(outside), outside,
                                        world), F(-1, 8))


class SettlementIsNotEnforcement(unittest.TestCase):
    """W11 — the negative control the settlement interface asks for."""

    def test_enforcement_leaves_no_residue_when_the_source_withdraws(self):
        demanded = Region(1, [Row([F(1)], F(1))])          # p(phi) >= 1
        trader = EnforcementTrader(demanded, F(1))
        self.assertEqual(contract_feasible_prices(trader, 4, F(0)), [(F(1),)])
        withdrawn = Region(1, [])
        free = [p for p in grid(1, 4) if max_gain((F(0),), p) <= 0]
        self.assertEqual(len(free), 5)
        self.assertTrue(withdrawn.contains((F(0),)))

    def test_a_settlement_constrains_every_later_date(self):
        """Stages are nested, so a settled sentence stays settled and the
        coherence polytope stays cut. That is a property of the record, not of
        anything the enforcement trader did."""
        later = {"phi": 1}
        self.assertEqual(NEGATION.pc_worlds(later), [(F(1), F(0))])
        self.assertFalse(coherence_membership((F(0), F(1)), NEGATION, later))
        region = Region(2, support_rows(NEGATION, later))
        self.assertFalse(region.contains((F(0), F(1))))

    def test_mispricing_a_settled_sentence_is_exploitable(self):
        """What makes the constraint stick over time is exploitation, not the
        enforcement position."""
        prices = [(F(1, 2), F(1, 2))] * 6
        worth = persistent_gap_trader_worth(prices, 0, [True] * 6, (F(1), F(0)))
        self.assertEqual(worth, F(3))

    def test_enforcement_supplies_no_report_and_no_payout(self):
        """The enforcement trader writes nothing into the record: its whole
        effect at a date is the coefficient vector, and the payout function is
        the world, which it does not touch."""
        region = Region(2, support_rows(NEGATION, {"phi": 1}))
        trader = EnforcementTrader(region, F(1))
        p = (F(1, 2), F(1, 2))
        before = set(NEGATION.pc_worlds({"phi": 1}))
        trader.coefficients(p)
        self.assertEqual(before, set(NEGATION.pc_worlds({"phi": 1})))


class EffectivePresentation(unittest.TestCase):
    """The compiler needs rows, and rows cost something to produce."""

    def test_row_count_grows_with_the_coefficient_bound(self):
        counts = [len(support_rows(BOOLEAN, {}, bound)) for bound in (1, 2)]
        self.assertEqual(counts, [80, 624])

    def test_rows_are_exact_rationals(self):
        for row in support_rows(BOOLEAN, {"phi": 1}):
            self.assertIsInstance(row.r, F)
            for c in row.c:
                self.assertIsInstance(c, F)

    def test_an_inconsistent_stage_has_no_presentation(self):
        with self.assertRaises(ValueError):
            support_rows(NEGATION, {"phi": 1, "notphi": 1})


if __name__ == "__main__":
    unittest.main()
