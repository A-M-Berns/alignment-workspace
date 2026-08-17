"""The two assessment models, and what separates them."""
from __future__ import annotations

import unittest
from fractions import Fraction as F

from deduction import support_rows
from enforcement import EnforcementTrader, Region, Row, grid
from market import Fragment, cube_vertices, holdings_value

FRAGMENT = Fragment(("phi", "notphi", "psi"), [lambda w: w[0] + w[1] == 1])


def live_worlds(region: Region, dimension: int):
    """The `{0,1}` vertices of the coherent admissible slice."""
    return [w for w in cube_vertices(dimension) if region.contains(w)]


class DeductiveRecovery(unittest.TestCase):
    """For the canonical deductive constraint the live worlds are `PC(D_t)`."""

    STAGES = ({}, {"phi": 1}, {"phi": 0}, {"phi": 1, "psi": 1})

    def test_live_worlds_equal_the_plausible_worlds(self):
        for settled in self.STAGES:
            region = Region(3, support_rows(FRAGMENT, settled))
            self.assertEqual(sorted(live_worlds(region, 3)),
                             sorted(FRAGMENT.pc_worlds(settled)), settled)

    def test_the_recovery_is_not_vacuous(self):
        """The stages genuinely differ, so the equality is not holding because
        every set is the same set."""
        sizes = [len(FRAGMENT.pc_worlds(s)) for s in self.STAGES]
        self.assertEqual(sizes, [4, 2, 2, 1])

    def test_the_slice_is_inside_propositional_coherence(self):
        """`S_t = Pi_t ∩ K_t` collapses to `K_t` for the deductive constraint,
        because the coherence polytope is already propositionally coherent."""
        for settled in self.STAGES:
            region = Region(3, support_rows(FRAGMENT, settled))
            for world in live_worlds(region, 3):
                self.assertEqual(world[0] + world[1], 1, settled)


class DerivedLiveWorldsLaunderTheLiability(unittest.TestCase):
    """Why the generalized assessment set cannot be read off the constraint
    alone: it reports zero liability for exactly the regions the deductive
    assessment set convicts."""

    REGION = Region(1, [Row([F(-1)], F(-1, 2))])        # K = {P <= 1/2}
    DEDUCTIVE = [(F(1),)]                               # `phi` settled true

    def setUp(self):
        self.trader = EnforcementTrader(self.REGION, F(10))

    def test_the_two_assessment_sets_are_disjoint_here(self):
        derived = live_worlds(self.REGION, 1)
        self.assertEqual(derived, [(F(0),)])
        self.assertEqual(self.DEDUCTIVE, [(F(1),)])
        self.assertEqual(set(derived) & set(self.DEDUCTIVE), set())

    def test_the_derived_set_reports_no_liability(self):
        worst = min(holdings_value(self.trader.coefficients(p), p, w)
                    for p in grid(1, 20) for w in live_worlds(self.REGION, 1))
        self.assertEqual(worst, 0)

    def test_the_deductive_set_reports_a_real_one(self):
        worst = min(holdings_value(self.trader.coefficients(p), p, w)
                    for p in grid(1, 20) for w in self.DEDUCTIVE)
        self.assertEqual(worst, F(-5, 8))

    def test_the_gap_is_the_whole_safety_question(self):
        """Anything derived from `K` alone gives the enforcement position
        nonnegative value, by the enforcement inequality — so the safety theorem
        stated over it is satisfied by construction."""
        for price in grid(1, 20):
            for world in live_worlds(self.REGION, 1):
                self.assertGreaterEqual(
                    holdings_value(self.trader.coefficients(price), price, world),
                    0, (price, world))


class LiftHypotheses(unittest.TestCase):
    """What a live-world process must supply for the source construction."""

    def test_the_deductive_process_is_nested(self):
        """The budgeter's induction needs a world plausible now to have been
        plausible before."""
        stages = [{}, {"phi": 1}, {"phi": 1, "psi": 1}]
        sets = [set(FRAGMENT.pc_worlds(s)) for s in stages]
        for earlier, later in zip(sets, sets[1:]):
            self.assertTrue(later <= earlier)

    def test_each_stage_is_finite_and_nonempty(self):
        for settled in ({}, {"phi": 1}, {"phi": 1, "psi": 1}):
            worlds = FRAGMENT.pc_worlds(settled)
            self.assertTrue(worlds)
            self.assertLess(len(worlds), 2 ** 3 + 1)

    def test_an_inconsistent_stage_is_empty_and_must_be_refused(self):
        self.assertEqual(FRAGMENT.pc_worlds({"phi": 1, "notphi": 1}), [])


if __name__ == "__main__":
    unittest.main()
