"""Exact fixtures A–L of the consolidation round's `COUNTERMODELS.md`."""
from __future__ import annotations

import itertools
import unittest
from fractions import Fraction as F

from src.authorship import blind, reason_mediated, selection_blind
from src.coverage import cov_fail, covered, mass, no_bind_live, rep_faithful
from src.regret import (activated, complete, expect, regret_U, regret_V, regret_auth,
                        void_mass)
from src.regret import mass as act_mass


class TestA_CompletionLowersRegret(unittest.TestCase):
    """The false lower bound R_U <= R_Vbar is refuted by a world-dependent strategy."""

    def test_refuted(self):
        pi = {0: F(1, 2), 1: F(1, 2)}
        C = lambda w: w == 0
        Vp = {0: {"a": F(1), "b": F(0)}}
        Vbar = complete(pi, C, Vp, "ab", lambda w, a: F(0) if a == "a" else F(1))
        alpha = {0: {"a": F(1), "b": F(0)}, 1: {"a": F(0), "b": F(1)}}
        RU = regret_U(pi, C, Vbar, alpha, "ab")
        RV = regret_V(pi, Vbar, alpha, "ab")
        self.assertEqual(RU, F(0))
        self.assertLess(RV, RU)


class TestB_LowerSharpness(unittest.TestCase):
    """`R_Vbar = R_U - D*eta` is attained (Lean `SharpLower.attained`)."""

    def test_attained(self):
        pi = {0: F(1, 2), 1: F(1, 2)}
        C = lambda w: w == 0
        Vp = {0: {"a": F(1), "b": F(0)}}
        Vbar = complete(pi, C, Vp, "ab", lambda w, a: F(0) if a == "a" else F(1))
        alpha = {0: {"a": F(1), "b": F(0)}, 1: {"a": F(0), "b": F(1)}}
        eta = void_mass(pi, C)
        self.assertEqual(regret_V(pi, Vbar, alpha, "ab"),
                         regret_U(pi, C, Vbar, alpha, "ab") - 1 * eta)

    def test_two_sided_sweep(self):
        pi = {0: F(1, 4), 1: F(1, 4), 2: F(1, 2)}
        grid = [F(0), F(1, 2), F(1)]
        for cbits in itertools.product([False, True], repeat=3):
            C = lambda w, cb=cbits: cb[w]
            eta = void_mass(pi, C)
            for va, vb in itertools.product(itertools.product(grid, repeat=3), repeat=2):
                Vbar = {w: {"a": va[w], "b": vb[w]} for w in pi}
                for aw in itertools.product([F(0), F(1)], repeat=3):
                    alpha = {w: {"a": aw[w], "b": 1 - aw[w]} for w in pi}
                    d = regret_V(pi, Vbar, alpha, "ab") - regret_U(pi, C, Vbar, alpha, "ab")
                    self.assertLessEqual(abs(d), eta)


class TestC_UpperSharpness(unittest.TestCase):
    """`R_Vbar = R_U + D*eta` is attained (PR #92's `Sharp.transfer_sharp`)."""

    def test_attained(self):
        pi = {0: F(3, 4), 1: F(1, 4)}
        C = lambda w: w == 0
        Vp = {0: {"a": F(1, 2), "b": F(1, 2)}}
        Vbar = complete(pi, C, Vp, "ab", lambda w, a: F(1) if a == "a" else F(0))
        alpha = {w: {"a": F(0), "b": F(1)} for w in pi}
        self.assertEqual(regret_V(pi, Vbar, alpha, "ab"),
                         regret_U(pi, C, Vbar, alpha, "ab") + void_mass(pi, C))


class TestAuthoritative(unittest.TestCase):
    """`R_auth <= eps / (1 - eta)` and the identity, on a sweep."""

    def test_bound(self):
        pi = {0: F(1, 4), 1: F(1, 4), 2: F(1, 2)}
        grid = [F(0), F(1, 2), F(1)]
        for cbits in itertools.product([False, True], repeat=3):
            if not any(cbits):
                continue
            C = lambda w, cb=cbits: cb[w]
            eta = void_mass(pi, C)
            if eta >= 1:
                continue
            for va, vb in itertools.product(itertools.product(grid, repeat=3), repeat=2):
                Vp = {w: {"a": va[w], "b": vb[w]} for w in pi if C(w)}
                Vbar = complete(pi, C, Vp, "ab", lambda w, a: F(0))
                for aw in itertools.product([F(0), F(1)], repeat=3):
                    alpha = {w: {"a": aw[w], "b": 1 - aw[w]} for w in pi}
                    RU = regret_U(pi, C, Vbar, alpha, "ab")
                    RA = regret_auth(pi, C, Vp, alpha, "ab")
                    self.assertEqual(RU, act_mass(pi, C) * RA)
                    eps = max(RU, F(0))
                    self.assertLessEqual(RA, eps / (1 - eta))


class TestD_EarlierManipulation(unittest.TestCase):
    """Terminal session mediated; an earlier disposition write flips V with the same trace."""

    def test_session_local_passes_diachronic_fails(self):
        # continuation = (early, late); trace records the terminal argument only
        beta = lambda q, z: q
        R = lambda w: w[1] == "argue"
        V = lambda w: F(1) if w[0] == "write" else F(0)
        D = [(e, l) for e in ("none", "write") for l in ("argue", "silent")]
        self.assertFalse(reason_mediated(beta, R, V, D, "z"))
        # session-local: the early write is part of the session policy z_s
        beta_s = lambda l, e: (e, l)
        for e in ("none", "write"):
            self.assertTrue(reason_mediated(beta_s, R, V, ["argue", "silent"], e))


class TestE_DiachronicLearning(unittest.TestCase):
    def test_trace_records_the_proof(self):
        beta = lambda q, z: q
        R = lambda w: (w[0] == "proof", w[1] == "argue")
        V = lambda w: F(1) if w[0] == "proof" else F(0)
        D = [(e, l) for e in ("none", "proof") for l in ("argue", "silent")]
        self.assertTrue(reason_mediated(beta, R, V, D, "z"))
        self.assertNotEqual(V(("proof", "silent")), V(("none", "silent")))

    def test_transient_reason(self):
        beta = lambda q, z: q
        final_state = lambda w: ()
        trace = lambda w: w == "argue_then_withdraw"
        V = lambda w: F(1) if w == "argue_then_withdraw" else F(0)
        D = ["never", "argue_then_withdraw"]
        self.assertFalse(reason_mediated(beta, final_state, V, D, "z"))
        self.assertTrue(reason_mediated(beta, trace, V, D, "z"))


ONE = ["w"]


class TestF_ProtectedSuppression(unittest.TestCase):
    def test_omission_voids(self):
        d = {"active": lambda c, w: True, "rep": lambda c, w: c != "p",
             "in_trace": lambda c, w: c != "p"}
        C = lambda w: True
        self.assertFalse(covered(d, ["p"], ONE, C))
        self.assertFalse(no_bind_live(d, ["p"], ONE, C))
        # the only sound activation is C = 0
        self.assertTrue(covered(d, ["p"], ONE, lambda w: False))


class TestG_RouteWithoutBarrier(unittest.TestCase):
    def test_route_alone_does_not_cover(self):
        d = {"active": lambda c, w: True, "rep": lambda c, w: False,
             "in_trace": lambda c, w: False}
        route_exists = True                     # RO supplies this (CovState.Covered)
        C = lambda w: True                      # evaluator commits before representation
        self.assertTrue(route_exists)
        self.assertFalse(no_bind_live(d, ["p"], ONE, C))
        self.assertFalse(covered(d, ["p"], ONE, C))


class TestH_BarrierWithoutRoute(unittest.TestCase):
    def test_soundness_with_vacuous_availability(self):
        d = {"active": lambda c, w: True, "rep": lambda c, w: False,
             "in_trace": lambda c, w: False}
        C = lambda w: False                     # every route destroyed: never certifies
        self.assertTrue(no_bind_live(d, ["p"], ONE, C))
        self.assertTrue(covered(d, ["p"], ONE, C))
        pi = {"w": F(1)}
        self.assertEqual(mass(pi, lambda w: not C(w)), F(1))   # eta = 1


class TestI_RepresentationUnfaithful(unittest.TestCase):
    def test_bridge_needed(self):
        d = {"active": lambda c, w: True, "rep": lambda c, w: True,
             "in_trace": lambda c, w: False}
        C = lambda w: True
        self.assertTrue(no_bind_live(d, ["p"], ONE, C))
        self.assertFalse(rep_faithful(d, ["p"], ONE))
        self.assertFalse(covered(d, ["p"], ONE, C))


class TestJ_UnprotectedDisclosure(unittest.TestCase):
    def test_outside_scope_is_not_a_violation(self):
        d = {"active": lambda c, w: True, "rep": lambda c, w: c == "p",
             "in_trace": lambda c, w: c == "p"}
        C = lambda w: True
        self.assertTrue(covered(d, ["p"], ONE, C))
        self.assertFalse(d["in_trace"]("u", "w"))


class TestK_SelectionLeakage(unittest.TestCase):
    def test_whole_continuation_depends_on_selection(self):
        beta = lambda q, z: q
        R = lambda w: w[1]
        V = lambda w: {"a": F(1), "b": F(0)}[w[1]]
        D = [(s, o) for s in "ab" for o in "ab"]
        self.assertTrue(reason_mediated(beta, R, V, D, "z"))
        # blind to the selection coordinate alone …
        self.assertTrue(blind(beta, R, [(("a", "a"), ("b", "a"))], "z"))
        # … but not to the selection-induced pair class under the leaking policy
        leak = lambda s: (s, s)
        self.assertFalse(blind(beta, R, [(leak("a"), leak("b"))], "z"))
        self.assertFalse(selection_blind(beta, V, leak, "ab", "z"))
        # the Value pathology: the selected candidate is punished
        pi = {0: F(1)}
        for sel in "ab":
            Vsel = {0: {a: F(0) if a == sel else F(1) for a in "ab"}}
            EU = {a: expect(pi, activated(lambda w: True, Vsel, a)) for a in "ab"}
            self.assertLess(EU[sel], max(EU.values()))


class TestL_ConsiderationNotAgreement(unittest.TestCase):
    def test_protected_objection_represented_verdict_free(self):
        d = {"active": lambda c, w: True, "rep": lambda c, w: True,
             "in_trace": lambda c, w: True}
        C = lambda w: True
        self.assertTrue(rep_faithful(d, ["objection_for_b"], ONE))
        self.assertTrue(no_bind_live(d, ["objection_for_b"], ONE, C))
        self.assertTrue(covered(d, ["objection_for_b"], ONE, C))
        # the principal still chooses a: nothing in coverage reads the verdict
        V = {"w": {"a": F(1), "b": F(0)}}
        self.assertEqual(max(V["w"], key=V["w"].get), "a")


class TestVoidMassBound(unittest.TestCase):
    def test_suppression_mass_le_void_mass(self):
        worlds = ["s", "t", "u"]
        pi = {"s": F(1, 2), "t": F(1, 4), "u": F(1, 4)}
        d = {"active": lambda c, w: True, "rep": lambda c, w: w != "u",
             "in_trace": lambda c, w: w != "u"}
        C = lambda w: w == "s"                   # sound: certified only where covered
        self.assertTrue(covered(d, ["p"], worlds, C))
        fail = lambda w: cov_fail(d, ["p"], w)
        self.assertEqual(mass(pi, fail), F(1, 4))
        self.assertLessEqual(mass(pi, fail), mass(pi, lambda w: not C(w)))


if __name__ == "__main__":
    unittest.main()
