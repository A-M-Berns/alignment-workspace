"""Conflict visibility, and whether the certificate carries provenance.

Invariant package item 12, and dispatch §8's three states.
"""
from __future__ import annotations

import unittest
from fractions import Fraction as Q

import variants as v
from conflict import (EliminationBudget, Infeasible, LinCon, certify,
                      cube_constraints, decide, feasible, from_rows)


class TheThreeStatesAreDistinguished(unittest.TestCase):

    def test_A_malformed(self):
        from pipeline import run_day
        run = run_day(2, v.base_stage(v.x0()),
                      v._std([("s", v.constant_false_injunction())]))
        self.assertEqual(run.conflict.state, "A-malformed")
        self.assertEqual(run.conflict.malformed[0][0], "s")

    def test_A_self_inconsistent(self):
        from pipeline import run_day
        run = run_day(2, v.base_stage(v.x0()),
                      v._std([("s", v.self_inconsistent_injunction())]))
        self.assertEqual(run.conflict.state, "A-self-inconsistent")
        sid, cert = run.conflict.self_inconsistent[0]
        self.assertEqual(sid, "s")
        self.assertIsInstance(cert, Infeasible)

    def test_B_empty_intersection_of_individually_satisfiable_injunctions(self):
        from pipeline import run_day
        run = v.empty_intersection()
        self.assertEqual(run.conflict.state, "B-empty-intersection")
        for sid, J in run.projection:
            alone = run_day(run.day, v.base_stage(v.x0()), v._std([(sid, J)]))
            self.assertEqual(alone.conflict.state, "none",
                             "each is satisfiable on its own")

    def test_C_normatively_consistent_but_incompatible_with_deduction(self):
        run = v.incompatible_with_deduction()
        self.assertEqual(run.conflict.state, "C-incompatible-with-deduction")
        self.assertIsInstance(run.conflict.incompatible, Infeasible)

    def test_no_conflict_on_the_happy_path(self):
        run = v.syntactically_fine_but_inadmissible()
        self.assertEqual(run.conflict.state, "none")


class CertificatesCarryProvenance(unittest.TestCase):
    """A finite infeasibility certificate names the injunction terms."""

    def test_empty_intersection_names_both_standings(self):
        cert = v.empty_intersection().conflict.normatively_empty
        standings = {tag[0] for tag in cert.multipliers if tag[0] != "cube"}
        self.assertEqual(standings, {"s:low", "s:high"})

    def test_self_inconsistency_names_both_inequality_indices(self):
        from pipeline import run_day
        run = run_day(2, v.base_stage(v.x0()),
                      v._std([("s", v.self_inconsistent_injunction())]))
        cert = run.conflict.self_inconsistent[0][1]
        indices = {tag[2] for tag in cert.multipliers
                   if isinstance(tag, tuple) and tag[0] == "s"}
        self.assertEqual(indices, {0, 1})

    def test_incompatibility_names_the_injunction_and_the_hull(self):
        cert = v.incompatible_with_deduction().conflict.incompatible
        sources = {tag[0] for tag in cert.multipliers}
        self.assertIn("s:cap", sources)
        self.assertIn("hull", sources)


class CertificatesRecheckExactly(unittest.TestCase):
    """The certificate is verified against the original rows, not trusted."""

    def test_a_farkas_certificate_satisfies_both_identities(self):
        cons = [
            LinCon((Q(1), Q(0)), Q(-1), ((("a", 0), Q(1)),)),
            LinCon((Q(-1), Q(0)), Q(-1), ((("b", 0), Q(1)),)),
        ]
        cert = feasible(cons, 2)
        self.assertIsInstance(cert, Infeasible)
        self.assertTrue(certify(cons, cert, 2))

    def test_a_tampered_certificate_is_rejected(self):
        cons = [
            LinCon((Q(1), Q(0)), Q(-1), ((("a", 0), Q(1)),)),
            LinCon((Q(-1), Q(0)), Q(-1), ((("b", 0), Q(1)),)),
        ]
        cert = feasible(cons, 2)
        bad = Infeasible({("a", 0): Q(1)}, cert.residual)
        self.assertFalse(certify(cons, bad, 2))

    def test_a_certificate_with_a_zero_multiplier_is_rejected(self):
        cons = [
            LinCon((Q(1), Q(0)), Q(-1), ((("a", 0), Q(1)),)),
            LinCon((Q(-1), Q(0)), Q(-1), ((("b", 0), Q(1)),)),
        ]
        bad = Infeasible({("a", 0): Q(0), ("b", 0): Q(1)}, Q(-2))
        self.assertFalse(certify(cons, bad, 2))


class DecisionAgreesWithElimination(unittest.TestCase):
    """The fast nonemptiness test and the elimination give the same verdict.

    `decide` answers "nonempty" by finding a basic feasible solution and falls
    through to elimination only when there is none. The two must not disagree,
    and on bounded systems they do not.
    """

    def cases(self):
        X = v.x0()
        out = []
        for name, J in (("cap", v.self_inconsistent_injunction()),
                        ("ok", v.j0(X))):
            from waist import kappa
            c = kappa([("s", J)], 2)
            d = len(c.coords)
            out.append((name, from_rows(c.rows, d) + cube_constraints(d), d))
        return out

    def test_same_verdict(self):
        for name, cons, d in self.cases():
            quick = decide(cons, d)
            slow = feasible(cons, d)
            self.assertEqual(quick is None, slow is None, name)


class TheEliminationCapIsRaisedNotIgnored(unittest.TestCase):
    """A budget overrun is an error; a silently truncated search is not."""

    def test_a_tiny_cap_raises(self):
        X = v.x0()
        from waist import kappa
        c = kappa([("s", v.j0(X))], 3)
        d = len(c.coords)
        with self.assertRaises(EliminationBudget):
            feasible(from_rows(c.rows, d) + cube_constraints(d), d, cap=1)


if __name__ == "__main__":
    unittest.main()
