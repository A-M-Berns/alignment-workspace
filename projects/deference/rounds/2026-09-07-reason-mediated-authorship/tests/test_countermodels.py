"""Exact fixtures A–K of `COUNTERMODELS.md`, plus the identity and invariance sweeps."""
from __future__ import annotations

import itertools
import unittest
from fractions import Fraction as F

from src.authorship import (authored, blind, chi, exclusive_bind, factor_map, reason_mediated,
                            selection_blind)
from src.regret import (activated, complete, expect, mass, regret_U, regret_V, regret_auth,
                        void_mass)

# Worlds are interventions; one principal policy `z`.
BETA = lambda q, z: q
Z = "z"


def const(v):
    return lambda w: v


class TestA_LegitimateInfluence(unittest.TestCase):
    """A supplies a proof; the reasons change; the verdict changes radically; authored."""

    def test_holds(self):
        D = ["silent", "proof"]
        R = lambda w: {"silent": (), "proof": ("proof",)}[w]
        V = lambda w: {"silent": F(0), "proof": F(1)}[w]
        author = const("principal")
        self.assertTrue(authored(BETA, R, V, author, D, Z))
        self.assertEqual(factor_map(BETA, R, V, D, Z), {(): F(0), ("proof",): F(1)})
        self.assertNotEqual(V("silent"), V("proof"))


class TestB_DirectWrite(unittest.TestCase):
    def test_fails(self):
        D = ["honest", "covert"]
        R = const(("argument",))                  # the write leaves the reasons unchanged
        V = lambda w: {"honest": F(1), "covert": F(0)}[w]
        self.assertTrue(exclusive_bind(BETA, const("principal"), D, Z))
        self.assertFalse(reason_mediated(BETA, R, V, D, Z))
        self.assertIsNone(factor_map(BETA, R, V, D, Z))


class TestC_Coercion(unittest.TestCase):
    def test_fails(self):
        D = ["argue", "argue+threat"]
        R = const(("argument",))                  # the threat is not an admitted reason
        V = lambda w: {"argue": F(1), "argue+threat": F(0)}[w]
        prohibited = [("argue", "argue+threat")]
        self.assertTrue(blind(BETA, R, prohibited, Z))
        self.assertFalse(blind(BETA, V, prohibited, Z))
        self.assertFalse(reason_mediated(BETA, R, V, D, Z))


class TestD_OverRichR(unittest.TestCase):
    """`R` records the whole intervention: mediation is vacuous and buys nothing."""

    def test_vacuous(self):
        D = ["honest", "covert"]
        R = lambda w: w                           # injective
        V = lambda w: {"honest": F(1), "covert": F(0)}[w]
        self.assertTrue(reason_mediated(BETA, R, V, D, Z))
        self.assertFalse(blind(BETA, R, [("honest", "covert")], Z))
        self.assertFalse(blind(BETA, V, [("honest", "covert")], Z))


class TestE_UnderRichR(unittest.TestCase):
    """`R` omits the proof: the honest argument is reported as manipulation."""

    def test_false_alarm(self):
        D = ["silent", "proof"]
        R = const(())
        V = lambda w: {"silent": F(0), "proof": F(1)}[w]
        self.assertFalse(reason_mediated(BETA, R, V, D, Z))
        # the same session with the proof recorded is authored
        R2 = lambda w: {"silent": (), "proof": ("proof",)}[w]
        self.assertTrue(reason_mediated(BETA, R2, V, D, Z))


class TestF_BindInsufficient(unittest.TestCase):
    def test_bind_without_mediation(self):
        D = ["honest", "covert"]
        R = const(("argument",))
        V = lambda w: {"honest": F(1), "covert": F(0)}[w]
        author = const("principal")               # P signs whatever was steered
        self.assertTrue(exclusive_bind(BETA, author, D, Z))
        self.assertFalse(authored(BETA, R, V, author, D, Z))


class TestG_MediationInsufficient(unittest.TestCase):
    def test_mediation_without_bind(self):
        D = ["honest", "write"]
        R = lambda w: {"honest": ("argument",), "write": ()}[w]
        V = lambda w: F(1) if R(w) else F(0)      # V = F(R): A computed it
        author = lambda w: {"honest": "principal", "write": "advisor"}[w]
        self.assertTrue(reason_mediated(BETA, R, V, D, Z))
        self.assertFalse(exclusive_bind(BETA, author, D, Z))
        self.assertFalse(authored(BETA, R, V, author, D, Z))


class TestH_SelectionLeakage(unittest.TestCase):
    """No literal preview, but the selection leaks through the advisor's other input."""

    def test_leak(self):
        # q = (selection, other input); the reason view sees only the other input
        beta = lambda q, z: q
        R = lambda w: w[1]
        V = lambda w: {"a": F(1), "b": F(0)}[w[1]]   # the verdict tracks the other input
        D = [(s, o) for s in "ab" for o in "ab"]
        self.assertTrue(reason_mediated(beta, R, V, D, Z))
        self.assertTrue(blind(beta, R, [(("a", "a"), ("b", "a"))], Z))   # no preview
        leak = lambda s: (s, s)
        sealed = lambda s: (s, "a")
        self.assertFalse(selection_blind(beta, V, leak, "ab", Z))
        self.assertTrue(selection_blind(beta, V, sealed, "ab", Z))

    def test_leak_reproduces_the_value_pathology(self):
        # under the leaking policy the payload punishes the selected candidate
        pi = {0: F(1)}
        for sel in "ab":
            V = {0: {a: F(0) if a == sel else F(1) for a in "ab"}}
            C = lambda w: True
            EU = {a: expect(pi, activated(C, V, a)) for a in "ab"}
            self.assertLess(EU[sel], max(EU.values()))   # the selection is never an argmax


class TestI_PartialEvaluation(unittest.TestCase):
    """Totalizing V is arbitrary; activated U is invariant; the regret interval is exact."""

    pi = {0: F(3, 4), 1: F(1, 4)}
    C = staticmethod(lambda w: w == 0)
    Vp = {0: {"a": F(1, 2), "b": F(1, 2)}}       # defined only on the certified world
    cands = "ab"
    alpha = {0: {"a": F(0), "b": F(1)}, 1: {"a": F(0), "b": F(1)}}   # follow b

    def completions(self):
        grid = [F(0), F(1, 2), F(1)]
        for fa, fb in itertools.product(grid, repeat=2):
            yield complete(self.pi, self.C, self.Vp, self.cands,
                           lambda w, a, fa=fa, fb=fb: fa if a == "a" else fb)

    def test_activated_invariant(self):
        tables = [{a: [activated(self.C, Vbar, a)(w) for w in self.pi] for a in self.cands}
                  for Vbar in self.completions()]
        self.assertTrue(all(t == tables[0] for t in tables))

    def test_regret_interval(self):
        # Corrected by the consolidation round: for a world-INDEPENDENT strategy the
        # completion regret lies in [R_U, R_U + eta]; the general statement is the
        # two-sided |R_V - R_U| <= D*eta (see the consolidation round's fixtures A, B).
        eta = void_mass(self.pi, self.C)
        RU = {regret_U(self.pi, self.C, Vbar, self.alpha, self.cands)
              for Vbar in self.completions()}
        self.assertEqual(RU, {F(0)})
        RVs = [regret_V(self.pi, Vbar, self.alpha, self.cands) for Vbar in self.completions()]
        self.assertEqual(min(RVs), F(0))            # candidate-constant completions
        self.assertEqual(max(RVs), F(0) + eta)      # the anti-selection completion
        self.assertTrue(all(abs(r - F(0)) <= eta for r in RVs))

    def test_authoritative_regret_is_completion_free(self):
        p = mass(self.pi, self.C)
        RA = regret_auth(self.pi, self.C, self.Vp, self.alpha, self.cands)
        for Vbar in self.completions():
            self.assertEqual(regret_U(self.pi, self.C, Vbar, self.alpha, self.cands), p * RA)


class TestJ_UnrelatedIntegrityFailure(unittest.TestCase):
    """Occurrence 1 vanishes from the record; occurrence 0's account propagates."""

    def test_local_trace_exists_global_step_does_not(self):
        start = {"exposed": {0, 1}, "accounts": {0: ("live", 0), 1: ("live", 1)}}
        end = {"exposed": {0}, "accounts": {0: ("live", 0)}}
        global_ok = start["exposed"] <= end["exposed"]           # exposure must not shrink
        local_ok = 0 in end["exposed"] and end["accounts"][0] == ("live", 0)
        self.assertFalse(global_ok)
        self.assertTrue(local_ok)


class TestK_SelectiveFailure(unittest.TestCase):
    """`C = 0` exactly on anti-A worlds; the sharp `D·η` transfer holds for every completion."""

    def test_sharp(self):
        for eta in [F(1, 2), F(1, 4), F(1, 8)]:
            pi = {"agree": 1 - eta, "disagree": eta}
            C = lambda w: w == "agree"
            Vp = {"agree": {"a": F(1, 2), "b": F(1, 2)}}
            alpha = {w: {"a": F(0), "b": F(1)} for w in pi}
            RU = regret_U(pi, C, complete(pi, C, Vp, "ab", lambda w, a: F(0)), alpha, "ab")
            self.assertEqual(RU, F(0))
            worst = complete(pi, C, Vp, "ab", lambda w, a: F(1) if a == "a" else F(0))
            self.assertEqual(regret_V(pi, worst, alpha, "ab"), RU + eta)
            for fa, fb in itertools.product([F(0), F(1, 3), F(1)], repeat=2):
                Vbar = complete(pi, C, Vp, "ab", lambda w, a, fa=fa, fb=fb: fa if a == "a" else fb)
                self.assertLessEqual(regret_V(pi, Vbar, alpha, "ab"), RU + eta)


class TestIdentities(unittest.TestCase):
    def test_regretU_eq_mass_regretAuth_sweep(self):
        pi = {0: F(1, 4), 1: F(1, 4), 2: F(1, 2)}
        grid = [F(0), F(1, 2), F(1)]
        for cbits in itertools.product([False, True], repeat=3):
            if not any(cbits):
                continue
            C = lambda w, cb=cbits: cb[w]
            for va, vb in itertools.product(itertools.product(grid, repeat=3), repeat=2):
                Vp = {w: {"a": va[w], "b": vb[w]} for w in pi if C(w)}
                for aw in [F(0), F(1, 3), F(1)]:
                    alpha = {w: {"a": aw, "b": 1 - aw} for w in pi}
                    Vbar = complete(pi, C, Vp, "ab", lambda w, a: F(1, 7))
                    self.assertEqual(regret_U(pi, C, Vbar, alpha, "ab"),
                                     mass(pi, C) * regret_auth(pi, C, Vp, alpha, "ab"))

    def test_perturbation(self):
        pi = {0: F(1, 2), 1: F(1, 2)}
        C = lambda w: True
        alpha = {w: {"a": F(1, 2), "b": F(1, 2)} for w in pi}
        V = {0: {"a": F(1), "b": F(0)}, 1: {"a": F(0), "b": F(1)}}
        delta = F(1, 5)
        V2 = {0: {"a": F(4, 5), "b": F(1, 5)}, 1: {"a": F(1, 5), "b": F(4, 5)}}
        r1, r2 = regret_U(pi, C, V, alpha, "ab"), regret_U(pi, C, V2, alpha, "ab")
        self.assertLessEqual(abs(r1 - r2), 2 * delta * mass(pi, C))

    def test_chi(self):
        D = ["honest", "covert", "proof"]
        R = lambda w: {"honest": (), "covert": (), "proof": ("proof",)}[w]
        V = lambda w: {"honest": F(1), "covert": F(3, 5), "proof": F(0)}[w]
        d = lambda x, y: abs(x - y)
        self.assertEqual(chi(BETA, R, V, D, Z, "honest", d), F(2, 5))
        self.assertEqual(chi(BETA, R, V, D, Z, "proof", d), F(0))


if __name__ == "__main__":
    unittest.main()
