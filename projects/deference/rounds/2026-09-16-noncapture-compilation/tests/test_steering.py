"""The trace-steering algebra: the identity, the bound, sharpness, and the sixteen attacks."""

import unittest
from fractions import Fraction as Q

from src.model import (A, T3, REASON, ROUTE, World, Program, entry, canon, N_form, N_full,
                       audit, security, advantage, bound, d_canon, kappa_form, mismatch,
                       both, identity_rhs)
from src.attacks import fixtures, base_world, canonical_program, W, IFACE


class Algebra(unittest.TestCase):

    def test_identity_and_bound_on_every_fixture(self):
        for f in fixtures():
            w, p = f.world, f.prog
            adv = advantage(p, f.steered, f.comparator, w)
            self.assertEqual(adv, identity_rhs(p, f.steered, f.comparator, w), f.name)
            self.assertLessEqual(adv, bound(p, f.steered, f.comparator, w), f.name)

    def test_extensional_program_has_zero_form_term(self):
        w, p = base_world(), canonical_program()
        for f in fixtures():
            if f.prog.extensional():
                self.assertEqual(kappa_form(f.prog, f.steered, f.world), Q(0), f.name)

    def test_form_steering_is_exactly_kappa(self):
        # fixtures 3, 4, 5: content identical, advantage = κ_form
        for f in fixtures():
            if f.name.split()[0] in ("3", "4", "5"):
                r = f.report()
                self.assertEqual(r["d_canon"], Q(0), f.name)
                self.assertEqual(r["advantage"], r["kappa"], f.name)
                self.assertEqual(r["advantage"], W, f.name)

    def test_mismatch_sharpness(self):
        # one trace that passes the audit while its comparator fails: a forged route in the
        # comparator direction is impossible (N never forges), so build the mismatch by a
        # comparator that lacks a protected reason the steered trace carries
        w = base_world()
        p = Program({"for": Q(1), "p_against": Q(0)}, base=Q(0))
        steered = (entry(A, REASON, "for"), entry(T3, REASON, "p_against"))
        comparator = (entry(A, REASON, "for"),)
        self.assertTrue(audit(steered, w)); self.assertFalse(audit(comparator, w))
        self.assertEqual(mismatch(steered, comparator, w), Q(1))
        self.assertEqual(advantage(p, steered, comparator, w), Q(1))
        self.assertEqual(bound(p, steered, comparator, w, D=Q(1)), Q(1))

    def test_reverse_mismatch_is_free(self):
        w = base_world()
        p = canonical_program()
        steered = (entry(A, REASON, "for"),)                       # void: protected missing
        comparator = N_full(steered, w)                             # passes
        self.assertLess(advantage(p, steered, comparator, w), Q(0))
        self.assertEqual(bound(p, steered, comparator, w), Q(0))


class Attacks(unittest.TestCase):

    def test_which_hypothesis_fails(self):
        table = {f.name.split()[0]: f.report() for f in fixtures()}
        # caught by a clause (advantage ≤ 0, steered void or fully informed)
        for k in ("1", "10", "12"):
            self.assertFalse(table[k]["audit_steered"], k)
            self.assertLessEqual(table[k]["advantage"], Q(0), k)
        # residual survives every clause: truthful selection within the declared interface
        for k in ("2", "13"):
            self.assertTrue(table[k]["audit_steered"] and table[k]["audit_comparator"], k)
            self.assertEqual(table[k]["advantage"], W, k)
            self.assertEqual(table[k]["kappa"], Q(0), k)
            self.assertGreater(table[k]["d_canon"], Q(0), k)
        # form attacks are charged to κ and removed by canonicalization
        for k in ("3", "4", "5"):
            self.assertEqual(table[k]["advantage"], table[k]["kappa"], k)
        self.assertEqual(table["11"]["advantage"], Q(0))
        self.assertEqual(table["11"]["kappa"], Q(0))
        # world change, granularity, inquiry, program quality: no reason-side advantage
        for k in ("6", "8", "14", "15"):
            self.assertEqual(table[k]["advantage"], Q(0), k)
        # the undeclared read is charged to the form term, not to content
        self.assertEqual(table["7"]["advantage"], W)
        self.assertEqual(table["7"]["kappa"], W)
        # an authentication-soundness failure is content discrepancy against N_full
        self.assertTrue(table["12b"]["audit_steered"])
        self.assertEqual(table["12b"]["advantage"], W)
        self.assertEqual(table["12b"]["d_canon"], Q(2))
        self.assertEqual(table["12b"]["kappa"], Q(0))
        # liveness failure of an unprotected reason is content discrepancy, not void
        self.assertEqual(table["9"]["advantage"], W)
        self.assertTrue(table["9"]["audit_steered"])
        # dynamics: the residual relative to a declared transform
        self.assertEqual(table["16"]["advantage"], W)

    def test_all_clauses_hold_yet_steering_remains(self):
        """The minimal counterexample to the literal two-interface thesis: fixture 2."""
        f = [f for f in fixtures() if f.name.startswith("2 ")][0]
        w, p = f.world, f.prog
        self.assertTrue(p.extensional())                      # canonicalization
        self.assertTrue(audit(f.steered, w))                   # authentication, authorship, coverage
        self.assertTrue(all(e[2] in w.iface for e in f.steered if e[1] == REASON))  # interface
        self.assertTrue(all(dict(e[3]).get("t", 0) <= 100 for e in f.steered))       # liveness
        self.assertEqual(advantage(p, f.steered, f.comparator, w), W)

    def test_total_scope_repairs_the_counterexample(self):
        """Protecting every declared reason type turns the omission into a void."""
        w = World({"for": True, "against": True, "p_against": True, "noise": True},
                  protected=IFACE)
        p = canonical_program()
        steered = (entry(A, REASON, "for"), entry(T3, REASON, "p_against"))
        self.assertFalse(audit(steered, w))
        self.assertLessEqual(advantage(p, steered, N_full(steered, w), w), Q(0))

    def test_total_scope_forces_full_content(self):
        """`content_residual_zero_of_total_scope`: under total scope and sound authentication,
        an audited trace has the true declared set as its canonical content."""
        w = World({"for": True, "against": True, "p_against": True, "noise": False},
                  protected=IFACE)
        p = canonical_program()
        for steered in [(entry(A, REASON, "for"), entry(T3, REASON, "against"), entry(T3, REASON, "p_against")),
                        (entry(T3, REASON, "p_against"), entry(A, REASON, "for"), entry(A, REASON, "for"),
                         entry(T3, REASON, "against", frame="urgent"))]:
            self.assertTrue(audit(steered, w))
            self.assertEqual(canon(steered, w), w.true_declared())
            self.assertEqual(d_canon(steered, N_full(steered, w), w), Q(0))
            self.assertEqual(advantage(p, steered, N_full(steered, w), w), Q(0))

    def test_supplied_reason_repairs_the_counterexample(self):
        """A third party supplying the omitted reason before the deadline removes it too."""
        w = base_world()
        p = canonical_program()
        steered = (entry(A, REASON, "for"), entry(T3, REASON, "p_against"), entry(T3, REASON, "against"))
        self.assertEqual(advantage(p, steered, N_full(steered, w), w), Q(0))


class RobustOpennessDecidable(unittest.TestCase):

    def test_declared_transform_class_is_a_finite_computation(self):
        """Over a finite declared class of log transforms, the audit verdict on every
        transformed trace is a finite family of computations."""
        w = base_world()
        p = canonical_program()
        steered = (entry(A, REASON, "for"), entry(T3, REASON, "against"), entry(T3, REASON, "p_against"))
        silent = lambda t: tuple(e for e in t if e[0] != A)
        jam = lambda t: tuple(e for e in t if e[2] != "p_against")
        transforms = [silent, jam, lambda t: t]
        verdicts = [audit(tr(steered), w) for tr in transforms]
        self.assertEqual(verdicts, [True, False, True])
        values = [p.value(tr(steered), w) for tr in transforms]
        self.assertEqual(values, [Q(0), Q(1, 2), Q(1, 4)])


if __name__ == "__main__":
    unittest.main()
