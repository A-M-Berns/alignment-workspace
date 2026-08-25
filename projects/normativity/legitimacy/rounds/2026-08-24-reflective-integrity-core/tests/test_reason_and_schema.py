"""Inference-step licensing is provenance; practical schemas are semantics.

`G3` reads the standing named by `steps(D_a)` and asks one question of it: is
it an active authorisation at the strict pre-state. It never applies the
schema interpreter to it, and nothing in RI asserts that the derivation is
sound. The effect comes from a different object entirely — the one named by
`schemaRef`, which is the only place the interpreter is used.
"""
from __future__ import annotations

import unittest

from ri_core import (History, PAuth, Standing, Supersede, WFError,
                     standing_tag, setting, superseding, ACTIVE, SUSPENDED)
import scenarios as S


class TestLicensingProvenance(unittest.TestCase):
    def test_licensed_steps_are_checked_against_the_strict_pre_state(self):
        h = S.licensed_inference_history()
        a = [e for e in h.norm_events() if e.id == "a1"][0]
        self.assertEqual(frozenset(["lic:modus"]), a.derivation.steps)
        licence = h.std(a.tau - 1)["lic:modus"]
        self.assertEqual("Active", licence.kind)
        self.assertIsInstance(licence.payload, PAuth)

    def test_a_suspended_inference_licence_refuses_the_event(self):
        seed = S.seed_from({
            "x": S.commitment("x"),
            "auth:sup": PAuth(superseding("sup", ["x"], [S.commitment("x2")])),
            "lic:modus": PAuth(S.creating("never-run", [S.commitment("k")])),
            "auth:susp": PAuth(setting("susp", ["lic:modus"], SUSPENDED)),
        }, debtor="A")
        h = History(seed)
        h.reason("e1", target="q")
        h.norm("a0", "auth:susp", author="A")
        from ri_core import Derivation
        d = Derivation("q", frozenset(["e1"]), frozenset(["lic:modus"]))
        with self.assertRaises(WFError) as caught:
            h.norm("a1", "auth:sup", author="A", derivation=d)
        self.assertEqual("G3", caught.exception.clause)

    def test_the_licence_code_is_never_interpreted(self):
        """`lic:modus` carries a code that would create standing if it were
        run. The event's effect is the supersession named by `schemaRef`, and
        no `Create` appears anywhere in the trajectory."""
        h = S.licensed_inference_history()
        a = [e for e in h.norm_events() if e.id == "a1"][0]
        eff = h.effect(a)
        self.assertIsInstance(eff, Standing)
        self.assertIsInstance(eff.alpha, Supersede)
        self.assertEqual({"x"}, set(eff.alpha.X))
        self.assertEqual(1, len([x for x in h.std() if x.startswith("@")]))

    def test_ri_does_not_assert_inferential_soundness(self):
        """The derivation concludes `q` from a reason bearing on it. RI checks
        that the reason is in the record and the step licence is active. It
        forms no opinion about whether `q` follows."""
        h = S.licensed_inference_history()
        a = [e for e in h.norm_events() if e.id == "a1"][0]
        self.assertEqual(frozenset(["e1"]), h.basis(a))
        self.assertEqual("q", a.derivation.concl)
        self.assertTrue(h.grounding_conservation())
        self.assertNotIn("q", h.bhat())      # concluding it endorses nothing

    def test_a_reason_appended_after_the_event_cannot_be_its_basis(self):
        seed = S.seed_from({
            "x": S.commitment("x"),
            "auth:sup": PAuth(superseding("sup", ["x"], [])),
        }, debtor="A")
        h = History(seed)
        from ri_core import Derivation
        d = Derivation("q", frozenset(["e-later"]), frozenset())
        with self.assertRaises(WFError) as caught:
            h.norm("a1", "auth:sup", author="A", derivation=d)
        self.assertEqual("G2", caught.exception.clause)


class TestSchemaInterface(unittest.TestCase):
    def test_effect_is_a_function_of_the_selected_schema_and_pre_state(self):
        h = S.supersession_history()
        a = [e for e in h.norm_events()][0]
        self.assertEqual(h.effect(a), h.effect(a))
        self.assertEqual(("Terminated", "a1"), h.status("x"))

    def test_schema_reference_is_resolved_before_any_effect_is_evaluated(self):
        """G4 precedes evaluation: an unresolvable `schemaRef` is refused
        without the interpreter ever being reached."""
        h = History(S.seed_from({"x": S.commitment("x")}))
        with self.assertRaises(WFError) as caught:
            h.norm("a1", "no-such-authority", author="A")
        self.assertEqual("G4", caught.exception.clause)

    def test_a_non_auth_payload_cannot_license_an_event(self):
        h = History(S.seed_from({"x": S.commitment("x")}))
        with self.assertRaises(WFError) as caught:
            h.norm("a1", "x", author="A")
        self.assertEqual("G4", caught.exception.clause)

    def test_empty_schema_instantiation_admits_no_normative_event(self):
        """The degenerate instantiation: no `PAuth` standing anywhere, so no
        Norm step is well-formed and every theorem holds vacuously."""
        h = History(S.seed_from({"x": S.commitment("x")}))
        h.settle("s1")
        h.reason("e1", s_L=frozenset(["s1"]), target="p")
        self.assertEqual((), h.norm_events())
        self.assertTrue(h.good())
        with self.assertRaises(WFError):
            h.norm("a1", "x", author="A")


if __name__ == "__main__":
    unittest.main()
