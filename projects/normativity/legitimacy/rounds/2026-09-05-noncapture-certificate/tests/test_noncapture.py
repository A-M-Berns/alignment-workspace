"""Every Boolean in the ledgers is recomputed here.  A passing suite pins the fixtures;
it is not a proof of the interface theorem, which is `NonCaptureCertificate.lean`."""
from __future__ import annotations

import unittest
from fractions import Fraction

import fixtures as F
from noncapture import (certificate, certificate_holds, coalition_holds_all_standing,
                        coverage_actual, faithful_closure, implements_everywhere,
                        robust_open, terminal_discharge_by)

MINIMAL_CLAUSES = ("S", "R+", "P")
COMPONENT_CLAUSES = ("S", "Ra", "Rb", "Rc", "P")


class InterfaceTheorem(unittest.TestCase):
    def test_theorem_holds_on_every_fixture_in_both_readings(self):
        for s in F.ALL:
            for reading in ("anchored", "internal"):
                if coverage_actual(s, reading) and certificate_holds(s, reading):
                    self.assertTrue(robust_open(s, reading), (s.name, reading))

    def test_nonvacuity(self):
        s = F.F0
        self.assertTrue(coverage_actual(s))
        self.assertTrue(all(certificate(s)[k] for k in MINIMAL_CLAUSES))
        self.assertTrue(robust_open(s))
        self.assertEqual(len(s.counterfactual), 3)

    def test_replacement_form_is_weaker_and_still_sufficient(self):
        for s in F.ALL:
            c = certificate(s)
            if c["R"]:
                self.assertTrue(c["R+"], s.name)
            if coverage_actual(s) and c["S"] and c["R+"] and c["P"]:
                self.assertTrue(robust_open(s), s.name)
        c = certificate(F.EXTERIOR_VARIED_DESTROY)
        self.assertFalse(c["R"])
        self.assertTrue(c["R+"])


class Necessity(unittest.TestCase):
    """One attack per clause: actual coverage and every other clause hold; Robust
    Openness fails."""

    def check_component_attack(self, s, dropped):
        c = certificate(s)
        self.assertTrue(coverage_actual(s), s.name)
        self.assertFalse(c[dropped], (s.name, dropped))
        for k in COMPONENT_CLAUSES:
            if k != dropped:
                self.assertTrue(c[k], (s.name, k))
        self.assertFalse(robust_open(s), s.name)

    def test_each_component_clause_has_an_attack(self):
        for dropped, scenarios in F.ATTACKS.items():
            for s in scenarios:
                self.check_component_attack(s, dropped)

    def test_each_minimal_clause_has_an_attack(self):
        attacks = {"S": F.A_S_ACTIVATE, "R+": F.A_RA, "P": F.A_P}
        for dropped, s in attacks.items():
            c = certificate(s)
            self.assertTrue(coverage_actual(s), s.name)
            self.assertFalse(c[dropped], (s.name, dropped))
            self.assertTrue(all(c[k] for k in MINIMAL_CLAUSES if k != dropped))
            self.assertFalse(robust_open(s), s.name)

    def test_silent_prefix_has_two_arms(self):
        a, b = F.ATTACKS["S"]
        self.assertFalse(a.actual.active())          # never active on the actual prefix
        self.assertTrue(b.actual.active() and b.actual.rep())   # active and represented

    def test_route_components_are_independent(self):
        # In each component attack the other two components of the same route survive.
        for dropped in ("Ra", "Rb", "Rc"):
            (s,) = F.ATTACKS[dropped]
            (cf,) = s.counterfactual.values()
            surviving = {"Ra": cf.route_admissible("audit"),
                         "Rb": cf.route_exposes("audit"),
                         "Rc": cf.route_registers("audit")}
            self.assertFalse(surviving[dropped])
            self.assertTrue(all(v for k, v in surviving.items() if k != dropped))

    def test_standing_attack_leaves_the_party_free_half_intact(self):
        s = F.A_P
        self.assertTrue(implements_everywhere(s))
        self.assertFalse(robust_open(s))
        (cf,) = s.counterfactual.values()
        self.assertTrue(coalition_holds_all_standing(cf, frozenset({F.V, F.W})))
        self.assertFalse(coalition_holds_all_standing(s.actual, frozenset({F.V, F.W})))


class ApplicabilityReading(unittest.TestCase):
    def test_internal_reading_makes_the_conclusion_empty(self):
        s = F.FORGET
        self.assertTrue(robust_open(s, "internal"))
        self.assertTrue(certificate_holds(s, "internal"))
        self.assertFalse(robust_open(s, "anchored"))
        self.assertFalse(certificate_holds(s, "anchored"))
        (cf,) = s.counterfactual.values()
        self.assertTrue(cf.rel_anchored())
        self.assertFalse(cf.rel_internal())


class NotClauses(unittest.TestCase):
    def test_disposition_is_governed_by_standing(self):
        with_p, without_p = F.DISPOSE_WITH_P, F.DISPOSE_WITHOUT_P
        for s in (with_p, without_p):
            (cf,) = s.counterfactual.values()
            self.assertTrue(cf.disposed and cf.rel_anchored() and not cf.active())
            self.assertTrue(implements_everywhere(s))
        self.assertTrue(robust_open(with_p))
        self.assertFalse(robust_open(without_p))
        self.assertEqual([k for k in MINIMAL_CLAUSES if not certificate(without_p)[k]], ["P"])

    def test_anchoring_is_a_requirement_on_the_semantics(self):
        # Same destroyed sensor; a semantics that re-anchors the target passes.
        self.assertTrue(robust_open(F.REANCHOR))
        self.assertFalse(robust_open(F.DESTROY_ANCHORED))
        (cf,) = F.REANCHOR.counterfactual.values()
        self.assertTrue(cf.route_exposes("audit"))       # a constant target is "exposed" by nothing
        self.assertEqual(set(cf.target.values()), {0})

    def test_settlement_timing_is_invisible_to_openness(self):
        s = F.SETTLEMENT
        self.assertTrue(robust_open(s))
        self.assertTrue(all(certificate(s)[k] for k in MINIMAL_CLAUSES))
        fates = terminal_discharge_by(s, Fraction(10))
        self.assertEqual(fates, {"actual": True, "prompt": True, "delayed": False, "never": False})

    def test_evaluator_capture_is_outside_openness(self):
        s = F.EVALUATOR
        self.assertTrue(robust_open(s))
        (cf,) = s.counterfactual.values()
        self.assertFalse(faithful_closure(cf))
        self.assertTrue(faithful_closure(s.actual))


class ExteriorHeldFixed(unittest.TestCase):
    def test_null_intervention_is_charged_when_the_exterior_varies(self):
        self.assertTrue(robust_open(F.EXTERIOR_FIXED_NULL))
        self.assertFalse(robust_open(F.EXTERIOR_VARIED_NULL))

    def test_destruction_is_excused_when_the_exterior_compensates(self):
        s = F.EXTERIOR_VARIED_DESTROY
        (cf,) = s.counterfactual.values()
        self.assertFalse(cf.route_exposes("delegate"))
        self.assertTrue(robust_open(s))
        self.assertFalse(certificate(s)["R"])


if __name__ == "__main__":
    unittest.main()
