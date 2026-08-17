"""Provenance ancestry and the branching-safe answerability object."""

from __future__ import annotations

import unittest
from itertools import product

import attacks as A
import forest as F
from provenance import (CONFERRED, DERIVED, Ground, GroundStore, INTERSECTION,
                        UNION, amplifies, ancestry, provenance_valid)


ROOT_A = Ground("r1", 0, "ra", frozenset({"x"}), origin=CONFERRED,
                filed_by="settlement")
ROOT_B = Ground("r2", 0, "rb", frozenset({"y"}), origin=CONFERRED,
                filed_by="settlement")


class AncestryTests(unittest.TestCase):

    def test_a_self_filed_root_is_refused(self):
        """The one thing a reasoner may never do: write down its own authority."""
        store = GroundStore((Ground("g", 0, "c", frozenset({"x"}),
                                    origin=CONFERRED, filed_by="reasoner"),))
        verdict = provenance_valid(store, "g", "x", 0)
        self.assertFalse(verdict.valid)
        self.assertEqual(verdict.code, "provenance.unconferred_root")

    def test_derivation_is_free_and_amplification_is_not(self):
        """Content may be new; scope may not grow."""
        same = Ground("g", 1, "new-content", frozenset({"x"}), basis=("r1",))
        wider = Ground("h", 1, "new-content", frozenset({"x", "y"}), basis=("r1",))
        store = GroundStore((ROOT_A, same, wider))
        self.assertTrue(provenance_valid(store, "g", "x", 1).valid)
        self.assertEqual(provenance_valid(store, "h", "y", 1).code,
                         "provenance.scope_amplified")

    def test_a_cycle_is_a_verdict_and_not_a_hang(self):
        store = GroundStore((Ground("a", 1, "a", frozenset({"x"}), basis=("b",)),
                             Ground("b", 1, "b", frozenset({"x"}), basis=("a",))))
        self.assertEqual(ancestry(store, "a")[1], "provenance.cyclic_basis")

    def test_a_basis_may_not_be_contemporaneous(self):
        store = GroundStore((ROOT_A, Ground("g", 0, "c", frozenset({"x"}),
                                            basis=("r1",))))
        self.assertEqual(provenance_valid(store, "g", "x", 1).code,
                         "provenance.basis_not_earlier")


class NoAmplificationTests(unittest.TestCase):
    """The statement the condition is supposed to make true, checked rather than
    asserted: no provenance-valid ground carries scope its roots were not
    granted."""

    def test_over_every_short_chain(self):
        conferred = {"r1": frozenset({"x"}), "r2": frozenset({"y"})}
        scopes = [frozenset(s) for s in ([], ["x"], ["y"], ["x", "y"])]
        checked = valid = 0
        for chain in product(scopes, repeat=3):
            grounds = [ROOT_A, ROOT_B]
            for index, scope in enumerate(chain):
                parent = "r1" if index == 0 else f"g{index - 1}"
                grounds.append(Ground(f"g{index}", index + 1, f"c{index}", scope,
                                      basis=(parent,)))
            store = GroundStore(tuple(grounds))
            checked += 1
            for coordinate in ("x", "y"):
                if provenance_valid(store, "g2", coordinate, 5).valid:
                    valid += 1
                    self.assertFalse(amplifies(store, "g2", conferred))
        self.assertEqual(checked, 4 ** 3)
        self.assertGreater(valid, 0)

    def test_the_two_scope_disciplines_differ(self):
        """A child of two parents with disjoint scopes: the union reading gives it
        joint jurisdiction neither parent had, the intersection reading gives it
        none.  Which is right depends on whether the constraint being licensed is
        coordinate-wise or joint, and nothing in the condition decides that."""
        child = Ground("g", 1, "c", frozenset({"x", "y"}), basis=("r1", "r2"))
        store = GroundStore((ROOT_A, ROOT_B, child))
        self.assertTrue(provenance_valid(store, "g", "x", 1, discipline=UNION).valid)
        self.assertEqual(
            provenance_valid(store, "g", "x", 1, discipline=INTERSECTION).code,
            "provenance.scope_amplified")


class ForestTests(unittest.TestCase):

    def test_a_single_label_loses_a_branch(self):
        """The previous round's fate object, shown incomplete on a split whose
        branches end differently."""
        label, leaves = F.label_loses_information()
        self.assertEqual(label, F.LEAF_LIVE)
        statuses = sorted(leaf.status for leaf in leaves)
        self.assertEqual(statuses, [F.LEAF_DISCHARGED, F.LEAF_LIVE])
        discharged = [l for l in leaves if l.status == F.LEAF_DISCHARGED]
        self.assertEqual(discharged[0].backing, "witness-a")

    def test_conservation_over_the_sweep(self):
        report = F.sweep(3)
        self.assertEqual(report.checked, 7 ** 3)
        self.assertEqual(report.accepted, 7 ** 3)
        self.assertGreater(report.mixed, 0)
        self.assertEqual(report.mixed, 36)
        self.assertEqual(report.label_disagrees, 20)

    def test_the_sweep_fails_on_its_null_input(self):
        report = F.sweep(3, well_formed=False)
        self.assertLess(report.accepted, report.checked)
        self.assertEqual(report.accepted, 89)

    def test_forest_composition(self):
        report = F.composition_sweep(2)
        self.assertGreater(report.pairs, 0)
        self.assertEqual(report.disagreements, ())
        self.assertEqual(report.pairs, report.agreements)


if __name__ == "__main__":
    unittest.main()
