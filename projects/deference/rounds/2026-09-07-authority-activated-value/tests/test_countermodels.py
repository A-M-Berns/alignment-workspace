"""Exact fixtures A–I of `COUNTERMODELS.md`, plus the transfer and reconstruction checks."""
from __future__ import annotations

import itertools
import unittest
from fractions import Fraction as F

from src.account import Law, Leaf, activated as acct_activated, activation, subst
from src.activated import (activated, activated_regret, argmax, cond_expect, expect,
                           threshold_expect, unactivated_regret, void_mass)


def menu(table):
    """`table[a][w]` -> callable `V(a, w)`."""
    return lambda a, w: F(table[a][w])


class TestA_CounterfactualOverreach(unittest.TestCase):
    """The no-AI human is wrong; the AI-informed principal is right and legitimate."""

    def test_reference_evaluator_defers_to_the_wrong_vector(self):
        pi = {0: F(1)}
        C = lambda w: True
        no_ai = menu({"a": {0: 1}, "b": {0: 0}})       # uninformed: prefers a
        informed = menu({"a": {0: 0}, "b": {0: 1}})    # after A's evidence: prefers b
        # the reference construction targets the counterfactual vector
        ref = argmax("ab", lambda a: expect(pi, activated(C, no_ai, a)))
        # the authority-activated construction targets the actual session
        aav = argmax("ab", lambda a: expect(pi, activated(C, informed, a)))
        self.assertEqual(ref, {"a"})
        self.assertEqual(aav, {"b"})
        # the actual principal's regret under each construction
        self.assertEqual(unactivated_regret(pi, informed, "ab", "a"), F(1))
        self.assertEqual(unactivated_regret(pi, informed, "ab", "b"), F(0))

    def test_counterfactual_vector_has_no_receipt(self):
        # only the actual session leaves an answer event in the history
        history = {7: {"a": F(0), "b": F(1)}}
        actual = Leaf("answered", event=7)
        c, v = activation(history, actual)
        self.assertEqual((c, v), (1, history[7]))
        # there is no account whose answer event carries the no-AI vector
        self.assertNotIn({"a": F(1), "b": F(0)}, history.values())


class TestB_ValueDependentCertification(unittest.TestCase):
    """Certification holds iff the answer is the desired one: the argmax flips."""

    pi = {0: F(1, 2), 1: F(1, 2)}
    V = staticmethod(menu({"a": {0: F(9, 10), 1: 0}, "b": {0: F(3, 5), 1: F(3, 5)}}))

    def test_flip(self):
        neutral = lambda w: True
        valdep = lambda w: self.V("a", w) >= F(3, 5)   # certify iff `a` scores well
        self.assertEqual(argmax("ab", lambda a: expect(self.pi, activated(neutral, self.V, a))),
                         {"b"})
        self.assertEqual(argmax("ab", lambda a: expect(self.pi, activated(valdep, self.V, a))),
                         {"a"})
        self.assertEqual(unactivated_regret(self.pi, self.V, "ab", "a"), F(3, 20))

    def test_factored_certificate_is_payload_blind(self):
        # process part reads only the process receipt; binding is total
        def cert_factored(proc_ok, V):
            return proc_ok  # exists a binding key for every V
        def cert_valdep(proc_ok, V):
            return proc_ok and V["a"] >= F(3, 5)
        V1, V2 = {"a": F(9, 10)}, {"a": F(0)}
        self.assertEqual(cert_factored(True, V1), cert_factored(True, V2))
        self.assertNotEqual(cert_valdep(True, V1), cert_valdep(True, V2))


class TestC_CherryPickedSession(unittest.TestCase):
    """Two sessions answer; choosing the convenient one flips the decision."""

    pi = {0: F(1)}
    V1 = staticmethod(menu({"a": {0: 1}, "b": {0: 0}}))
    V2 = staticmethod(menu({"a": {0: 0}, "b": {0: 1}}))

    def test_existential_semantics_is_gameable(self):
        C = lambda w: True
        pick1 = argmax("ab", lambda a: expect(self.pi, activated(C, self.V1, a)))
        pick2 = argmax("ab", lambda a: expect(self.pi, activated(C, self.V2, a)))
        self.assertEqual((pick1, pick2), ({"a"}, {"b"}))

    def test_designated_slot_pins_one_receipt(self):
        history = {11: {"a": F(1), "b": F(0)}, 12: {"a": F(0), "b": F(1)}}
        # the designated slot's port receives event 12; event 11 is at another port
        # and belongs to another occurrence
        designated = Leaf("answered", event=12)
        self.assertEqual(activation(history, designated), (1, history[12]))
        # two answer leaves under one occurrence (a split law) do not activate
        split = Law((Leaf("answered", event=11), Leaf("answered", event=12)), "split")
        self.assertFalse(acct_activated(split))

    def test_first_answer_binds(self):
        first = Leaf("answered", event=12)
        # no live port: a later step cannot add anything
        later = subst(first, {0: Leaf("answered", event=13)})
        self.assertEqual(later, first)


class TestD_PerActionCertification(unittest.TestCase):
    """Per-candidate certification breaks the conditional-argmax identity."""

    pi = {0: F(1, 2), 1: F(1, 2)}
    V = staticmethod(menu({"a": {0: F(3, 5), 1: F(3, 5)}, "b": {0: 1, 1: 1}}))

    def test_breaks(self):
        Ca = lambda w: True
        Cb = lambda w: w == 0
        EU = {"a": expect(self.pi, activated(Ca, self.V, "a")),
              "b": expect(self.pi, activated(Cb, self.V, "b"))}
        self.assertEqual(argmax("ab", EU.get), {"a"})
        self.assertEqual(argmax("ab", lambda a: expect(self.pi, lambda w: self.V(a, w))), {"b"})
        # the transfer bound survives with the worst void mass
        eta_max = max(void_mass(self.pi, Ca), void_mass(self.pi, Cb))
        self.assertLessEqual(unactivated_regret(self.pi, self.V, "ab", "a"), F(0) + eta_max)

    def test_common_activation_is_the_conditional_argmax(self):
        pi = {0: F(1, 3), 1: F(1, 3), 2: F(1, 3)}
        grid = [F(0), F(1, 2), F(1)]
        for va in itertools.product(grid, repeat=3):
            for vb in itertools.product(grid, repeat=3):
                V = menu({"a": dict(enumerate(va)), "b": dict(enumerate(vb))})
                for cbits in itertools.product([False, True], repeat=3):
                    if not any(cbits):
                        continue
                    C = lambda w, cb=cbits: cb[w]
                    act = argmax("ab", lambda a: expect(pi, activated(C, V, a)))
                    cond = argmax("ab", lambda a: cond_expect(pi, C, lambda w: V(a, w)))
                    self.assertEqual(act, cond)


class TestE_ClosedVsAnswered(unittest.TestCase):
    """A valid closure without an evaluation must not activate."""

    def test_closure_does_not_activate(self):
        closed = Leaf("closed", event=5)
        self.assertFalse(acct_activated(closed))
        self.assertEqual(activation({5: {"a": F(1)}}, closed), (0, None))

    def test_resolved_semantics_lets_the_agent_defer_to_itself(self):
        # a "resolved" reading with a default payload (the agent's own proposal)
        pi = {0: F(1)}
        default = menu({"a": {0: 1}, "b": {0: 0}})       # A's proposal
        principal = menu({"a": {0: 0}, "b": {0: 1}})     # never asked
        resolved = lambda w: True
        self.assertEqual(argmax("ab", lambda a: expect(pi, activated(resolved, default, a))),
                         {"a"})
        self.assertEqual(unactivated_regret(pi, principal, "ab", "a"), F(1))

    def test_carry_is_transparent(self):
        carried = Law((Law((Leaf("answered", event=9),), "carry"),), "re-represent")
        self.assertTrue(acct_activated(carried))
        self.assertEqual(activation({9: "V"}, carried), (1, "V"))


class TestF_VacuousActivation(unittest.TestCase):
    def test_always_void(self):
        pi = {0: F(1, 2), 1: F(1, 2)}
        V = menu({"a": {0: 1, 1: 1}, "b": {0: 0, 1: 0}})
        C = lambda w: False
        for sel in "ab":
            self.assertEqual(activated_regret(pi, C, V, "ab", sel), F(0))
        self.assertEqual(unactivated_regret(pi, V, "ab", "b"), F(1))
        self.assertEqual(void_mass(pi, C), F(1))   # the bound ε + η = 1 is vacuous


class TestG_SelectiveFailure(unittest.TestCase):
    """C fails exactly on the branches where the principal would disagree."""

    def fixture(self, eta):
        pi = {"agree": 1 - eta, "disagree": eta}
        V = menu({"a": {"agree": F(1, 2), "disagree": 1},
                  "b": {"agree": F(1, 2), "disagree": 0}})
        C = lambda w: w == "agree"
        return pi, V, C

    def test_damage_equals_void_mass(self):
        for eta in [F(1, 2), F(1, 4), F(1, 8), F(1, 100)]:
            pi, V, C = self.fixture(eta)
            self.assertEqual(activated_regret(pi, C, V, "ab", "b"), F(0))
            self.assertEqual(void_mass(pi, C), eta)
            self.assertEqual(unactivated_regret(pi, V, "ab", "b"), eta)

    def test_selection_dependent_refusal_is_charged_to_availability(self):
        # the principal refuses to answer whenever A selects `b`
        pi = {0: F(1)}
        V = menu({"a": {0: F(1, 2)}, "b": {0: 1}})
        for sel in "ab":
            C = lambda w, s=sel: s == "a"
            EU = {a: expect(pi, activated(C, V, a)) for a in "ab"}
            consistent = sel in argmax("ab", EU.get)
            if sel == "a":
                self.assertFalse(consistent)        # A would rather pick b
            else:
                self.assertTrue(consistent)         # tie at 0
                self.assertEqual(void_mass(pi, C), F(1))   # and nothing is activated


class TestH_UnrelatedGlobalFailure(unittest.TestCase):
    def test_local_holds_global_fails(self):
        # openness per state per concern
        states = ["s0", "s1", "s2"]
        open_ = {("s0", 0): True, ("s1", 0): True, ("s2", 0): True,
                 ("s0", 1): True, ("s1", 1): False, ("s2", 1): True}
        global_ok = all(open_[(s, c)] for s in states for c in (0, 1))
        local_ok = all(open_[(s, 0)] for s in states)
        endpoint_ok = all(open_[(s, c)] for s in ("s0", "s2") for c in (0, 1))
        self.assertFalse(global_ok)
        self.assertTrue(local_ok)
        self.assertTrue(endpoint_ok)   # endpoint-only would also accept it; not what is used


class TestI_SelfReference(unittest.TestCase):
    """The principal sees A's selection before committing."""

    pi = {0: F(1)}

    def test_preview_has_no_consistent_hard_selection(self):
        C = lambda w: True
        for sel in "ab":
            V = menu({a: {0: F(0) if a == sel else F(1)} for a in "ab"})
            EU = {a: expect(self.pi, activated(C, V, a)) for a in "ab"}
            self.assertNotIn(sel, argmax("ab", EU.get))

    def test_sealed_commitment_is_consistent(self):
        C = lambda w: True
        V = menu({"a": {0: 1}, "b": {0: 0}})   # committed before the reveal
        EU = {a: expect(self.pi, activated(C, V, a)) for a in "ab"}
        self.assertIn("a", argmax("ab", EU.get))
        self.assertEqual(unactivated_regret(self.pi, V, "ab", "a"), F(0))


class TestTransfer(unittest.TestCase):
    """`regret_V <= regret_U + η` on a sweep, and attained."""

    def test_sweep(self):
        pi = {0: F(1, 4), 1: F(1, 4), 2: F(1, 2)}
        grid = [F(0), F(1, 3), F(2, 3), F(1)]
        for va in itertools.product(grid, repeat=3):
            for vb in itertools.product(grid, repeat=3):
                V = menu({"a": dict(enumerate(va)), "b": dict(enumerate(vb))})
                for cbits in itertools.product([False, True], repeat=3):
                    C = lambda w, cb=cbits: cb[w]
                    eta = void_mass(pi, C)
                    for sel in "ab":
                        eps = activated_regret(pi, C, V, "ab", sel)
                        self.assertLessEqual(unactivated_regret(pi, V, "ab", sel), eps + eta)

    def test_attained(self):
        pi = {0: F(3, 4), 1: F(1, 4)}
        V = menu({"a": {0: F(1, 2), 1: 1}, "b": {0: F(1, 2), 1: 0}})
        C = lambda w: w == 0
        self.assertEqual(activated_regret(pi, C, V, "ab", "b"), F(0))
        self.assertEqual(unactivated_regret(pi, V, "ab", "b"), void_mass(pi, C))


class TestReconstruction(unittest.TestCase):
    """The threshold-security expectation reconstructs `E[C V]` within `1/k`."""

    def test_within_grid(self):
        pi = {0: F(1, 3), 1: F(1, 3), 2: F(1, 3)}
        V = menu({"a": {0: F(1, 7), 1: F(5, 7), 2: F(1)}})
        C = lambda w: w != 1
        target = expect(pi, activated(C, V, "a"))
        for k in (1, 2, 3, 5, 8, 13, 50):
            approx = threshold_expect(pi, C, V, "a", k)
            self.assertGreaterEqual(approx, target)
            self.assertLess(approx - target, F(1, k))


class TestWitnessMenuActivation(unittest.TestCase):
    """The constant option of a Total-Trust witness menu must carry the same activation."""

    def test_unactivated_constant_reopens_the_certifiability_channel(self):
        pi = {0: F(1, 2), 1: F(1, 2)}
        V = menu({"x": {0: 1, 1: 1}})               # the principal always values x at 1
        C = lambda w: w == 0                        # certified on half the mass
        s = F(3, 4)
        EU_x = expect(pi, activated(C, V, "x"))     # 1/2
        # against an unactivated constant the void branch favours the constant
        self.assertLess(EU_x, s)
        # against the activated constant the comparison is the conditional one
        self.assertGreater(EU_x, expect(pi, lambda w: (F(1) if C(w) else F(0)) * s))
        self.assertGreater(cond_expect(pi, C, lambda w: V("x", w)), s)


if __name__ == "__main__":
    unittest.main()
