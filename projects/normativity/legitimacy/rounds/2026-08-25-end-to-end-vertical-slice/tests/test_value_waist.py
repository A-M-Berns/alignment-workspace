"""The value waist: rigidity, non-exposure, plurality, and what it refuses.

Invariant package items 1-4.
"""
from __future__ import annotations

import unittest
from fractions import Fraction as Q

import variants as v
from toy import registry, x0, x1
from waist import (CertifiedLUV, Expect, Ineq, Injunction, NonExposure,
                   ValueRegistry, ValueSpec, kappa, luv_exposure)


class ValueSemanticStability(unittest.TestCase):
    """Item 1. The same query on the same specification is the same LUV."""

    def test_repeated_compilation_is_identical(self):
        reg = registry()
        self.assertEqual(reg.compile_value("v0", "q"),
                         reg.compile_value("v0", "q"))

    def test_a_quantity_is_named_after_its_specification(self):
        self.assertEqual(x0().luv.name, "X[v0:q]")
        self.assertEqual(x1().luv.name, "X[v1:q]")

    def test_two_specifications_expose_different_luvs_for_one_query(self):
        self.assertNotEqual(x0().luv, x1().luv)
        self.assertEqual(set(x0().luv.expect_affine(3).sentences())
                         & set(x1().luv.expect_affine(3).sentences()), set())


class HistoricalReferenceRigidity(unittest.TestCase):
    """Item 2. Admitting `v1` changes nothing about `X[v0:q]`."""

    def test_the_registry_refuses_to_rewrite_a_frozen_specification(self):
        self.assertIsInstance(v.rewriting_a_frozen_spec(), ValueError)

    def test_admitting_a_successor_does_not_move_the_predecessor(self):
        reg = ValueRegistry()
        reg.admit(ValueSpec("v0", {}, (
            ("q", luv_exposure("t0", {"low": Q(0), "high": Q(1)})),)))
        before = reg.compile_value("v0", "q")
        reg.admit(ValueSpec("v1", {}, (
            ("q", luv_exposure("t1", {"low": Q(0), "high": Q(1)})),),
            supersedes=("v0",)))
        self.assertEqual(before, reg.compile_value("v0", "q"))

    def test_no_expression_maps_a_historical_quantity_to_the_current_one(self):
        """The compiler takes a specification code, never "the active one".

        There is no argument to `compile_value` that means "whatever is in
        force", so the reinterpretation this invariant forbids has no way to be
        written.
        """
        reg = registry()
        with self.assertRaises(TypeError):
            reg.compile_value("v0")          # a query is not optional


class FailedExposureIsExplicit(unittest.TestCase):
    """Item 3. A query that cannot be quantified is a state, not a failure."""

    def test_a_declining_exposure_returns_a_non_exposure(self):
        out = v.failed_query()
        self.assertIsInstance(out, NonExposure)
        self.assertFalse(out.exposes)
        self.assertIn("common scale", out.reason)

    def test_an_unknown_query_is_a_non_exposure(self):
        self.assertIsInstance(v.unknown_query(), NonExposure)

    def test_an_unbounded_quantity_is_refused_at_the_waist(self):
        out = v.unbounded_exposure()
        self.assertIsInstance(out, NonExposure)
        self.assertIn("[0,1] LUV", out.reason)

    def test_non_exposure_is_non_destructive(self):
        """The specification keeps every other exposure it had."""
        reg = registry()
        reg.compile_value("v0", "incomparable")
        self.assertIsInstance(reg.compile_value("v0", "q"), CertifiedLUV)


class PluralValue(unittest.TestCase):
    """Several LUVs, no scalarisation, and a tradeoff only when declared."""

    def test_three_dimensions_are_three_luvs(self):
        dims = v.plural_value()["dims"]
        self.assertEqual(len(dims), 3)
        self.assertEqual(len({X.luv.name for X in dims.values()}), 3)

    def test_separate_ceilings_never_add_across_dimensions(self):
        dims, J = v.plural_separate_ceilings()
        c = kappa([("s", J)], 1)
        self.assertEqual(len(c.rows), 3)
        for row in c.rows:
            touched = {phi for phi, coeff in zip(c.coords, row.coefficients)
                       if coeff}
            owners = {phi.name.split(">")[0] for phi in touched}
            self.assertEqual(len(owners), 1)

    def test_a_tradeoff_is_one_declared_inequality(self):
        dims, J = v.plural_affine_tradeoff()
        c = kappa([("s", J)], 1)
        self.assertEqual(len(c.rows), 1)
        signs = {(-coeff > 0) for coeff in c.rows[0].coefficients if coeff}
        self.assertEqual(signs, {True, False},
                         "a tradeoff mixes signs; that is what makes it one")


class SeveralActiveSpecifications(unittest.TestCase):
    """Two active value specifications need no rule to choose between them."""

    def test_both_expose_and_neither_shadows_the_other(self):
        out = v.two_active_specs()
        self.assertIsInstance(out["XA"], CertifiedLUV)
        self.assertIsInstance(out["XB"], CertifiedLUV)
        self.assertNotEqual(out["XA"].luv, out["XB"].luv)

    def test_one_injunction_may_name_quantities_from_both(self):
        out = v.two_active_specs()
        J = Injunction("Jboth", (
            Ineq(((Q(1), Expect(out["XA"])), (Q(1), Expect(out["XB"]))),
                 rhs=Q(1)),))
        c = kappa([("s", J)], 1)
        self.assertEqual(len(c.coords), 4)


class TheOperativeLayerDoesNotReadProvenance(unittest.TestCase):
    """A value-generated LUV and a plain one are interchangeable downstream."""

    def test_compilation_ignores_origin(self):
        from li import LUV
        X = x0()
        plain = CertifiedLUV(LUV(X.luv.name), X.code_witness, X.values,
                             origin=())
        J1 = Injunction("J", (Ineq(((Q(1), Expect(X)),), rhs=Q(1, 2)),))
        J2 = Injunction("J", (Ineq(((Q(1), Expect(plain)),), rhs=Q(1, 2)),))
        a, b = kappa([("s", J1)], 2), kappa([("s", J2)], 2)
        self.assertEqual(a.coords, b.coords)
        self.assertEqual([r.coefficients for r in a.rows],
                         [r.coefficients for r in b.rows])


if __name__ == "__main__":
    unittest.main()
