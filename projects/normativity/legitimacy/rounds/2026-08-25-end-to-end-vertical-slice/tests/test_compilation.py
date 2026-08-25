"""Compilation exactness, and semantic rigidity of a frozen payload.

Invariant package items 9 (compilation exactness) and the semantic-rigidity
question §6 of the dispatch asks not to assert but to inspect.
"""
from __future__ import annotations

import unittest
from fractions import Fraction as Q

import li
import variants as v
from toy import PHI, j0, x0
from waist import Expect, Ineq, Injunction, Prob, kappa


class ExpectationIsTheThresholdBundle(unittest.TestCase):
    """`E_n(X)` is the precision-`n+1` bundle's day-`n` price, and nothing else."""

    def test_bundle_shape_matches_the_pinned_definition(self):
        X = x0().luv
        for k in (1, 2, 3, 5):
            form = X.expect_affine(k)
            self.assertEqual(form.const, Q(0))
            self.assertEqual(len(form.terms), k)
            self.assertEqual([c for c, _ in form.terms], [Q(1, k)] * k)
            self.assertEqual([s for _, s in form.terms],
                             [X.gt(Q(i, k)) for i in range(k)])

    def test_day_n_uses_grid_n_plus_one(self):
        X = x0().luv
        prices = {X.gt(r): Q(1) for r in li.merged_grid(range(6))}
        for n in range(5):
            self.assertEqual(X.expect(prices, n), Q(1))
            self.assertEqual(set(X.expect_affine(n + 1).sentences()),
                             {X.gt(r) for r in li.day_grid(n)})

    def test_expectation_lies_in_the_unit_interval(self):
        X = x0().luv
        for n in range(4):
            for value in (Q(0), Q(1, 3), Q(1)):
                prices = {s: value for s in X.expect_affine(n + 1).sentences()}
                self.assertTrue(Q(0) <= X.expect(prices, n) <= Q(1))


class CompiledRowsAgreeWithTheQuantities(unittest.TestCase):
    """A compiled row's value at a price vector is the inequality's own value."""

    def test_row_slack_is_the_inequality_slack(self):
        X = x0()
        J = j0(X)
        for n in (0, 1, 2, 3):
            c = kappa([("s", J)], n)
            prices = {phi: Q(1, 3) for phi in c.coords}
            point = tuple(prices[phi] for phi in c.coords)
            for row, ineq in zip(c.rows, J.ineqs):
                lhs = ineq.form(n).price(prices)
                self.assertEqual(row.slack(point), Q(ineq.rhs) - lhs)

    def test_expectation_term_compiles_to_the_expectation(self):
        X = x0()
        J = Injunction("Jx", (Ineq(((Q(1), Expect(X)),), rhs=Q(1, 2)),))
        for n in (0, 1, 2, 3):
            c = kappa([("s", J)], n)
            prices = {phi: Q(3, 4) for phi in c.coords}
            point = tuple(prices[phi] for phi in c.coords)
            independent = X.luv.expect(prices, n)
            self.assertEqual(-row_value(c.rows[0], point), independent)

    def test_probability_term_compiles_to_the_price(self):
        J = Injunction("Jp", (Ineq(((Q(1), Prob(PHI)),), rhs=Q(1, 2)),))
        c = kappa([("s", J)], 2)
        self.assertEqual(c.coords, (PHI,))
        self.assertEqual(c.rows[0].coefficients, (Q(-1),))
        self.assertEqual(c.rows[0].rhs, Q(-1, 2))


def row_value(row, point):
    return sum((c * p for c, p in zip(row.coefficients, point)), Q(0))


class SharedCoordinatesAreListedOnce(unittest.TestCase):
    """`nodup` survives a term that names another term's threshold sentence."""

    def test_prob_of_a_threshold_sentence_does_not_duplicate_a_coordinate(self):
        X = x0()
        collide = Prob(X.luv.gt(Q(0)))
        J = Injunction("Jcollide", (
            Ineq(((Q(1), Expect(X)), (Q(1), collide)), rhs=Q(3, 2)),))
        c = kappa([("s", J)], 1)
        self.assertEqual(len(c.coords), len(set(c.coords)))
        self.assertIn(X.luv.gt(Q(0)), c.coords)
        i = c.coords.index(X.luv.gt(Q(0)))
        self.assertEqual(c.rows[0].coefficients[i], -(Q(1, 2) + Q(1)))

    def test_two_luvs_sharing_a_threshold_merge_coefficients(self):
        X = x0()
        J = Injunction("Jsame", (
            Ineq(((Q(1), Expect(X)), (Q(1), Expect(X))), rhs=Q(1)),))
        c = kappa([("s", J)], 0)          # day 0: the grid is the single {0}
        self.assertEqual(len(c.coords), 1)
        self.assertEqual(c.rows[0].coefficients, (Q(-2),))


class SemanticRigidityOfAFrozenPayload(unittest.TestCase):
    """One payload, several days: the rows move and the meaning does not.

    Rigidity is stated as an identity on values rather than on syntax, because
    the syntax demonstrably differs: at day `n` the constraint is a row in
    `n + 2` coordinates and at day `n+1` it is a row in `n + 3`.
    """

    def test_row_systems_differ_in_dimension_across_days(self):
        _, _, runs = v.frozen_injunction_across_days(days=(0, 1, 2))
        dims = [len(runs[n].coords) for n in (0, 1, 2)]
        self.assertEqual(dims, [2, 3, 4])

    def test_every_day_compiles_to_the_same_condition_on_quantities(self):
        X, J, runs = v.frozen_injunction_across_days(days=(0, 1, 2))
        ineq = J.ineqs[0]
        for n, run in runs.items():
            row = run.compiled.rows[0]
            for value in (Q(0), Q(1, 4), Q(1, 2), Q(1)):
                prices = {phi: value for phi in run.coords}
                point = tuple(prices[phi] for phi in run.coords)
                quantity = X.luv.expect(prices, n) - prices[PHI]
                self.assertEqual(row.slack(point), Q(ineq.rhs) - quantity)

    def test_the_payload_itself_is_identical_across_days(self):
        _, J, runs = v.frozen_injunction_across_days(days=(0, 1, 2))
        for run in runs.values():
            self.assertEqual(run.projection[0][1], J)


if __name__ == "__main__":
    unittest.main()
