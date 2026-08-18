"""The core condition, compiled: from an endorsement and a coefficient to a trader."""
from __future__ import annotations

import unittest
from fractions import Fraction as F

from core import (compile_core_row, core_row_in_credal_space, indicator,
                  maximal_theta, priceable_coefficients,
                  satisfies_core_condition)
from enforcement import EnforcementTrader, Region, Row, contract_feasible_prices, grid
from market import Fragment

#: The settlement interface's displayed instance: three worlds, and three
#: sentences each true at exactly one of them, so a credal state and a price
#: vector carry the same information.
FRAGMENT = Fragment(("A", "B", "C"), [lambda w: w[0] + w[1] + w[2] == 1])
SIMPLEX = [Row((F(1), F(1), F(1)), F(1)), Row((F(-1), F(-1), F(-1)), F(-1))]


class Priceability(unittest.TestCase):
    """The one condition the bridge needs, and the honest failure when it fails."""

    def setUp(self):
        self.worlds = FRAGMENT.worlds()

    def test_an_endorsement_on_a_priced_sentence_is_priceable(self):
        c = indicator(FRAGMENT, "A", self.worlds)
        self.assertEqual(priceable_coefficients(c, FRAGMENT, self.worlds),
                         (F(1), F(0), F(0)))

    def test_an_unpriceable_coefficient_is_detected(self):
        one = Fragment(("A",), [])
        self.assertIsNone(priceable_coefficients((F(1), F(2)), one, one.worlds()))

    def test_the_compiler_declines_rather_than_enforcing_something_else(self):
        one = Fragment(("A",), [])
        with self.assertRaises(ValueError):
            compile_core_row((F(1), F(2)), F(1, 2), F(1, 4), one, one.worlds())


class AgreesWithTheInterfacesClosedForm(unittest.TestCase):
    """`NL-SI-A5` gives `(M - r) / (M - m)`; the module recomputes it."""

    def test_the_displayed_instance(self):
        worlds = FRAGMENT.worlds()
        c = indicator(FRAGMENT, "A", worlds)
        self.assertEqual(maximal_theta(c, F(1, 2), worlds), F(1, 2))

    def test_a_constant_row_admits_every_coefficient(self):
        worlds = FRAGMENT.worlds()
        self.assertIsNone(maximal_theta((F(1), F(1), F(1)), F(1), worlds))

    def test_an_unsatisfiable_endorsement_admits_none(self):
        worlds = FRAGMENT.worlds()
        c = indicator(FRAGMENT, "A", worlds)
        self.assertEqual(maximal_theta(c, F(3, 2), worlds), F(0))


class CompiledRowIsTheCoreCondition(unittest.TestCase):
    """The row is the minimum over shrunk vertices; the definition walks them all."""

    def setUp(self):
        self.worlds = FRAGMENT.worlds()
        self.c = indicator(FRAGMENT, "A", self.worlds)
        self.a = priceable_coefficients(self.c, FRAGMENT, self.worlds)
        self.rhs = F(1, 2)

    def credal_grid(self, denominator: int):
        return [p for p in grid(3, denominator) if sum(p) == 1]

    def test_row_and_definition_agree_pointwise(self):
        for theta in (F(1, 8), F(1, 4), F(1, 2)):
            row = compile_core_row(self.c, self.rhs, theta, FRAGMENT, self.worlds)
            region = Region(3, [row] + SIMPLEX)
            for price in self.credal_grid(6):
                self.assertEqual(
                    region.contains(price),
                    satisfies_core_condition(price, self.a, self.c, self.rhs,
                                             theta, self.worlds),
                    (theta, price))

    def test_the_compiled_row_is_the_expected_rational(self):
        row = compile_core_row(self.c, self.rhs, F(1, 4), FRAGMENT, self.worlds)
        self.assertEqual(row.c, (F(3, 4), F(0), F(0)))
        self.assertEqual(row.r, F(1, 2))          # p(A) >= 2/3

    def test_enforcement_delivers_core_admissible_prices(self):
        for theta in (F(1, 8), F(1, 4), F(1, 2)):
            row = compile_core_row(self.c, self.rhs, theta, FRAGMENT, self.worlds)
            region = Region(3, [row] + SIMPLEX)
            trader = EnforcementTrader(region, F(1))
            feasible = contract_feasible_prices(trader, 12, F(0))
            self.assertTrue(feasible, theta)
            for price in feasible:
                self.assertTrue(
                    satisfies_core_condition(price, self.a, self.c, self.rhs,
                                             theta, self.worlds), (theta, price))

    def test_at_the_maximal_coefficient_one_reference_survives(self):
        row = compile_core_row(self.c, self.rhs, F(1, 2), FRAGMENT, self.worlds)
        region = Region(3, [row] + SIMPLEX)
        trader = EnforcementTrader(region, F(1))
        self.assertEqual(contract_feasible_prices(trader, 12, F(0)),
                         [(F(1), F(0), F(0))])

    def test_the_credal_space_row_uses_the_vertex_minimum(self):
        _, right = core_row_in_credal_space(self.c, self.rhs, F(1, 4), self.worlds)
        self.assertEqual(right, F(1, 2))          # r - theta * 0
        self.assertEqual(min(sum(a * b for a, b in zip(self.c, w))
                             for w in self.worlds), F(0))

    def test_theta_outside_its_range_is_refused(self):
        for theta in (F(0), F(-1, 2), F(3, 2)):
            with self.assertRaises(ValueError):
                core_row_in_credal_space(self.c, self.rhs, theta, self.worlds)


if __name__ == "__main__":
    unittest.main()


class BoundaryCoefficient(unittest.TestCase):
    """`theta = 1` collapses the core condition to `0 >= r - m`.

    The compiler must not manufacture a satisfiable price row out of the
    unsatisfiable branch. It is the one place where declining is the correct
    output and a row would be a silent lie.
    """

    fragment = Fragment(("A", "B"))
    worlds = [(F(0), F(0)), (F(1), F(0)), (F(0), F(1)), (F(1), F(1))]

    def coefficient(self):
        return tuple(w[0] for w in self.worlds)          # min 0, max 1

    def test_satisfiable_branch_is_the_vacuous_row(self):
        row = compile_core_row(self.coefficient(), F(0), F(1),
                               self.fragment, self.worlds)
        self.assertEqual(row.r, F(0))
        self.assertTrue(all(x == 0 for x in row.c))
        for w in self.worlds:                            # satisfied everywhere
            self.assertEqual(row.violation(w), F(0))

    def test_unsatisfiable_branch_is_declined(self):
        with self.assertRaises(ValueError):
            compile_core_row(self.coefficient(), F(1, 2), F(1),
                             self.fragment, self.worlds)


class ConstantEndorsement(unittest.TestCase):
    """`M = m`: the endorsement is a constant on the simplex.

    Then no coefficient changes anything, and the two branches are opposite:
    automatically satisfied, or impossible. `maximal_theta` must not report
    "every theta works" for the impossible one.
    """

    worlds = [(F(0), F(0)), (F(1), F(1))]

    def test_constant_and_satisfied_admits_every_coefficient(self):
        self.assertIsNone(maximal_theta((F(1, 2), F(1, 2)), F(1, 3), self.worlds))

    def test_constant_and_impossible_admits_none(self):
        self.assertEqual(maximal_theta((F(1, 2), F(1, 2)), F(3, 4), self.worlds),
                         F(0))


class RankDeficientPriceability(unittest.TestCase):
    """Settlement shrinks the world list, and the linear system stops being square.

    A consistent but rank-deficient system has a solution, and rejecting it would
    call a priceable endorsement unpriceable — declining to enforce something the
    market can in fact express. An inconsistent one must still be refused.
    """

    def test_underdetermined_consistent_system_solves(self):
        fragment = Fragment(("A", "B", "C"))
        worlds = [(F(0), F(0), F(0)), (F(1), F(1), F(1))]   # 2 worlds, 3 names
        a = priceable_coefficients((F(0), F(5)), fragment, worlds)
        self.assertIsNotNone(a)
        for i, w in enumerate(worlds):
            self.assertEqual(sum(x * v for x, v in zip(a, w)),
                             (F(0), F(5))[i])

    def test_rank_deficient_consistent_system_solves(self):
        """Two priced sentences agreeing on every surviving world."""
        fragment = Fragment(("A", "B"))
        worlds = [(F(0), F(0)), (F(1), F(1))]               # A and B coincide
        a = priceable_coefficients((F(0), F(3)), fragment, worlds)
        self.assertIsNotNone(a)
        for i, w in enumerate(worlds):
            self.assertEqual(sum(x * v for x, v in zip(a, w)), (F(0), F(3))[i])

    def test_rank_deficient_inconsistent_system_is_refused(self):
        fragment = Fragment(("A", "B"))
        worlds = [(F(0), F(0)), (F(1), F(1))]
        # every combination of indicators is 0 at world 00; demanding 1 is not
        # a functional of the priced sentences on these worlds
        self.assertIsNone(priceable_coefficients((F(1), F(3)), fragment, worlds))

    def test_overdetermined_consistent_system_solves(self):
        fragment = Fragment(("A",))
        worlds = [(F(0),), (F(1),), (F(1),)]
        a = priceable_coefficients((F(0), F(2), F(2)), fragment, worlds)
        self.assertEqual(a, (F(2),))

    def test_overdetermined_inconsistent_system_is_refused(self):
        fragment = Fragment(("A",))
        worlds = [(F(1),), (F(1),)]
        self.assertIsNone(priceable_coefficients((F(2), F(3)), fragment, worlds))
