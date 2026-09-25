"""The identity, its conditions, the companion, activation, and the whole-run algebra."""

import unittest
from fractions import Fraction as Q

from src.authority import (W, M, v_r, xi_p, xi_v, xi_c, xi_d, o1, o2, bypass_gain,
                           outcome_gain, E, E_gain, E_xi, security, activation_terms,
                           mismatch_mass, nondelegation, consult_nonneg, legitimate,
                           chooser_bypasses, outcome_chooser_bypasses, argmax, node,
                           local_gap, nodewise_bypasses, ever_bypass_bound, drift,
                           global_value, hybrid_chain, hybrid_step_terms, rootE)


GRID = [Q(k, 2) for k in range(-4, 5)]


def all_worlds():
    for vu in GRID:
        for vp in GRID:
            for vm in GRID:
                for r in (True, False):
                    yield W(p=1, vu=vu, vp=vp, vm=vm, r=r)


class Identity(unittest.TestCase):

    def test_identity_on_a_grid(self):
        for w in all_worlds():
            self.assertEqual(bypass_gain(w), xi_d(w) - xi_c(w))
            self.assertEqual(xi_c(w), xi_p(w) + xi_v(w))
            self.assertGreaterEqual(xi_v(w), 0)
            self.assertGreaterEqual(xi_d(w), 0)

    def test_approve_branch_reduces_to_minus_provenance_premium(self):
        for w in all_worlds():
            if w["r"]:
                self.assertEqual(bypass_gain(w), -xi_p(w))
                self.assertEqual(xi_d(w), xi_v(w))

    def test_decline_branch_divergence_is_positive_part(self):
        for w in all_worlds():
            if not w["r"]:
                self.assertEqual(xi_d(w), max(w["vp"] - w["vm"], 0))
                self.assertEqual(xi_v(w), max(w["vm"] - w["vp"], 0))

    def test_divergence_zero_iff_argmax(self):
        for w in all_worlds():
            self.assertEqual(xi_d(w) == 0, v_r(w) == M(w))
            w2 = dict(w)
            w2["r"] = argmax(w)
            self.assertEqual(xi_d(w2), 0)

    def test_nondelegation_and_legitimacy_give_a_signed_conclusion(self):
        for w in all_worlds():
            if xi_p(w) >= 0 and xi_d(w) == 0:
                self.assertLessEqual(bypass_gain(w), 0)
                if xi_c(w) > 0:
                    self.assertLess(bypass_gain(w), 0)
            if xi_p(w) >= 0:
                self.assertLessEqual(bypass_gain(w), xi_d(w))

    def test_landed_dictionary(self):
        # landed ρ = (w_app − w_act)₊ = (ξ_d − ξ_v)₊ ; landed κ = (w_raw − w_app)₊ = (−ξ_p)₊
        pos = lambda x: x if x > 0 else Q(0)
        for w in all_worlds():
            self.assertEqual(pos(w["vp"] - v_r(w)), pos(xi_d(w) - xi_v(w)))
            self.assertEqual(pos(w["vu"] - w["vp"]), pos(-xi_p(w)))
            # the landed bound is never below the signed value, and drops ξ_v
            self.assertLessEqual(bypass_gain(w), pos(-xi_p(w)) + pos(xi_d(w) - xi_v(w)))


class Conditions(unittest.TestCase):
    """Three conditions of increasing weakness: per-world `ξ_p ≥ 0`, per-world `ξ_c ≥ 0`,
    expected `E[ξ_c] ≥ 0`.  The first two are separated by a decline world whose veto
    value covers a delay cost; the last two by predicted approval under delay."""

    def test_per_world_implication(self):
        for w in all_worlds():
            if xi_p(w) >= 0:
                self.assertGreaterEqual(xi_c(w), 0)

    def test_veto_covers_delay_separates_the_per_world_conditions(self):
        w = W(p=1, vu=2, vp=1, vm=3, r=False)
        self.assertEqual((xi_p(w), xi_v(w), xi_c(w), xi_d(w)), (-1, 2, 1, 0))
        self.assertFalse(nondelegation([w]))
        self.assertTrue(consult_nonneg([w]))
        self.assertEqual(bypass_gain(w), -1)

    def test_on_legitimate_approve_worlds_the_two_coincide(self):
        for w in all_worlds():
            if w["r"] and xi_d(w) == 0:
                self.assertEqual(xi_c(w), xi_p(w))

    def test_illegitimate_approval_leaves_the_gain_at_minus_provenance(self):
        w = W(p=1, vu=1, vp=0, vm=2, r=True)
        self.assertEqual((xi_d(w), xi_v(w), xi_c(w), xi_p(w)), (2, 2, 1, -1))
        self.assertTrue(consult_nonneg([w]))
        self.assertEqual(bypass_gain(w), 1)  # ξ_c ≥ 0 without ξ_d = 0 does not remove it

    def test_predicted_approval_separates_expectation_from_per_world(self):
        approve = dict(vu=2, vp=1, vm=0, r=True)
        decline = dict(vu=0, vp=0, vm=3, r=False)
        confident = [W(p=Q(4, 5), **approve), W(p=Q(1, 5), **decline)]
        unsure = [W(p=Q(1, 2), **approve), W(p=Q(1, 2), **decline)]
        for ws in (confident, unsure):
            self.assertTrue(legitimate(ws))
            self.assertFalse(consult_nonneg(ws))
        self.assertEqual(E_xi(confident, "c"), Q(-1, 5))
        self.assertEqual(E_xi(unsure, "c"), 1)
        self.assertEqual(E_gain(confident), Q(1, 5))
        self.assertEqual(E_gain(unsure), -1)
        self.assertTrue(chooser_bypasses(confident))
        self.assertFalse(chooser_bypasses(unsure))

    def test_belief_independence_under_nondelegation_and_legitimacy(self):
        ws = [W(p=Q(1, 3), vu=1, vp=2, vm=0, r=True), W(p=Q(2, 3), vu=1, vp=1, vm=3, r=False)]
        self.assertTrue(nondelegation(ws) and legitimate(ws))
        for p in (Q(0), Q(1, 7), Q(1, 2), Q(9, 10), Q(1)):
            ws[0]["p"], ws[1]["p"] = p, 1 - p
            self.assertLessEqual(E_gain(ws), 0)
            self.assertFalse(chooser_bypasses(ws))


class Companion(unittest.TestCase):

    def test_companion_identity_on_a_grid(self):
        for w in all_worlds():
            for qu, qp, qm in ((Q(3), Q(1), Q(-1)), (Q(0), Q(2), Q(2)), (Q(-1), Q(-2), Q(4))):
                w["qu"], w["qp"], w["qm"] = qu, qp, qm
                self.assertEqual(outcome_gain(w), xi_d(w) - xi_c(w) + o1(w) + o2(w))
                if w["r"]:
                    self.assertEqual(o2(w), 0)
                else:
                    self.assertEqual(o2(w), (qp - qm) - (w["vp"] - w["vm"]))

    def test_o1_is_the_provenance_value_when_delay_costs_agree(self):
        # matched continuations: the outcome difference of unasked vs approved release is
        # the delay saving d; the evaluator prices provenance at π and delay at d
        for d in (Q(0), Q(1, 2), Q(2)):
            for pi in (Q(0), Q(1), Q(3)):
                w = W(p=1, vu=5 + d - pi, vp=5, vm=0, r=True, qu=5 + d, qp=5, qm=0)
                self.assertEqual(xi_p(w), pi - d)
                self.assertEqual(o1(w), pi)

    def test_veto_value_is_forecast_invariant_and_outcome_veto_is_not(self):
        w = W(p=1, vu=0, vp=1, vm=2, r=False)
        for qp, qm in ((Q(1), Q(2)), (Q(3), Q(2)), (Q(10), Q(0))):
            w["qp"], w["qm"], w["qu"] = qp, qm, qp
            self.assertEqual(xi_v(w), 1)
        outcome_veto = lambda w: max(w["qp"], w["qm"]) - w["qp"]
        w["qp"], w["qm"] = Q(1), Q(2)
        self.assertEqual(outcome_veto(w), 1)
        w["qp"], w["qm"] = Q(3), Q(2)
        self.assertEqual(outcome_veto(w), 0)


class Activation(unittest.TestCase):

    def test_activation_identity(self):
        for au in (True, False):
            for aa in (True, False):
                for w in list(all_worlds())[::7]:
                    w["au"], w["aa"] = au, aa
                    lhs = security([w], True) - security([w], False)
                    common, raw_only, ask_only = activation_terms([w])
                    self.assertEqual(lhs, common + raw_only - ask_only)

    def test_activation_bound_with_width(self):
        D = Q(4)
        ws = [W(p=Q(1, 4), vu=4, vp=0, vm=0, r=True, au=True, aa=False),
              W(p=Q(1, 4), vu=1, vp=2, vm=3, r=False, au=True, aa=True),
              W(p=Q(1, 4), vu=0, vp=4, vm=4, r=True, au=False, aa=True),
              W(p=Q(1, 4), vu=2, vp=2, vm=2, r=False, au=False, aa=False)]
        lhs = security(ws, True) - security(ws, False)
        common, raw_only, ask_only = activation_terms(ws)
        self.assertLessEqual(lhs, common + D * mismatch_mass(ws))
        self.assertEqual(mismatch_mass(ws), Q(1, 4))
        self.assertEqual(raw_only, 1)  # attained: D · E[M] = 1

    def test_marginal_refuted_replicated(self):
        D = Q(3)
        ws = [W(p=Q(1, 2), vu=D, vp=0, vm=0, r=True, au=True, aa=False),
              W(p=Q(1, 2), vu=D, vp=0, vm=0, r=True, au=False, aa=True)]
        self.assertEqual(security(ws, True) - security(ws, False), D / 2)
        self.assertEqual(E(ws, lambda w: Q(1) if w["au"] else Q(0))
                         - E(ws, lambda w: Q(1) if w["aa"] else Q(0)), 0)
        self.assertEqual(mismatch_mass(ws), Q(1, 2))


class WholeRuns(unittest.TestCase):

    def test_sequential_bound_and_zero_case(self):
        run = [node(p=Q(1), vu=1, vp=2, vm=0, r=True),
               node(p=Q(1, 2), vu=2, vp=1, vm=3, r=False),      # veto covers delay: no bypass
               node(p=Q(1, 4), vu=2, vp=1, vm=0, r=False)]      # illegitimate decline: ξ_d = 1, ξ_c = −1
        gaps = [local_gap(n) for n in run]
        self.assertEqual(gaps, [-1, -1, 2])
        self.assertEqual([nodewise_bypasses(n) for n in run], [False, False, True])
        self.assertEqual(ever_bypass_bound(run), Q(1, 4))
        legit = run[:2]
        self.assertEqual(ever_bypass_bound(legit), 0)

    def test_recommitment_creates_drift_and_no_bypass(self):
        # day 3: a legitimate amendment reverses the ranking of the two responses
        day3 = node(p=Q(1), vu=1, vp=2, vm=3, r=False, vuE=1, vpE=3, vmE=2)
        day4 = node(p=Q(1, 2), vu=1, vp=2, vm=3, r=False, vuE=1, vpE=3, vmE=2)
        run = [day3, day4]
        for n in run:
            self.assertEqual(xi_d(n), 0)          # node-wise: legitimate, no bypass
            self.assertFalse(nodewise_bypasses(n))
            self.assertEqual(drift(n), 1)         # root evaluator disagrees with the recommendation
            self.assertEqual(xi_c(rootE(n)), 2)
        # the global comparison under the root evaluator prices each replacement as
        # p · (drift − ξ_c^E) and the deepest-first hybrid telescopes exactly
        bypass_set = {0, 1}
        values, order = hybrid_chain(run, bypass_set)
        terms = hybrid_step_terms(run, order)
        self.assertEqual(values[0] - values[-1], sum(terms))
        self.assertEqual(terms, [Q(1, 2) * (1 - 2), Q(1) * (1 - 2)])
        # asking dominates under nondelegation even with drift, since drift ≤ ξ_c^E here;
        # a larger drift than the consultation premium would reverse it
        self.assertLessEqual(values[0], values[-1])
        big = [node(p=Q(1), vu=1, vp=2, vm=3, r=False, vuE=1, vpE=5, vmE=0)]
        self.assertEqual(drift(big[0]), 5)
        v, o = hybrid_chain(big, {0})
        self.assertGreater(v[0], v[-1])
        self.assertEqual(v[0] - v[-1], drift(big[0]) - xi_c(rootE(big[0])))


if __name__ == "__main__":
    unittest.main()
