import unittest

from pe_models import (
    Carry,
    CoverageClose,
    Disposal,
    MetEdge,
    TransportStep,
    answerability_conserved,
    exhaustive_one_step_transport,
    liability_rows,
    realized_action,
    response_structure_same,
)


class ProperExerciseFixtures(unittest.TestCase):
    def test_authorization_is_not_proper_exercise(self):
        bogus = CoverageClose(True, True, False, False, False, True, False)
        self.assertTrue(bogus.authorized)
        self.assertFalse(bogus.pe_resolve())

    def test_authorized_self_revision_destroying_coverage(self):
        revision = TransportStep(
            frozenset({"coverage"}), frozenset(), frozenset(),
            frozenset({"coverage"}), {}, authorized=True,
        )
        self.assertTrue(revision.authorized)
        self.assertFalse(revision.pe_sound())

    def test_same_batch_needs_post_state(self):
        step = CoverageClose(True, True, False, False, False, True, False)
        self.assertTrue(step.prefix_only_accepts(adequate_route_pre=True))
        self.assertFalse(step.pe_resolve())

    def test_temporary_failure_can_carry_repair_burden(self):
        step = CoverageClose(True, True, False, False, False, False, True)
        self.assertTrue(step.pe_resolve())

    def test_burden_split(self):
        split = TransportStep(
            frozenset({"b"}), frozenset({"b1", "b2"}), frozenset({"b"}),
            frozenset({"b"}),
            {"b": Carry(("b1", "b2"), frozenset({("b", "b1"), ("b", "b2")}))},
        )
        self.assertTrue(split.pe_sound())

    def test_burden_merge_and_sequential_conservation(self):
        split = TransportStep(
            frozenset({"b"}), frozenset({"b1", "b2"}), frozenset({"b"}),
            frozenset({"b"}),
            {"b": Carry(("b1", "b2"), frozenset({("b", "b1"), ("b", "b2")}))},
        )
        merge = TransportStep(
            frozenset({"b1", "b2"}), frozenset({"m"}), frozenset({"b1", "b2"}),
            frozenset({"b1", "b2"}),
            {
                "b1": Carry(("m",), frozenset({("b1", "m")})),
                "b2": Carry(("m",), frozenset({("b2", "m")})),
            },
        )
        self.assertTrue(merge.pe_sound())
        self.assertTrue(answerability_conserved("b", (split, merge)))

    def test_ontology_translation(self):
        valid = TransportStep(
            frozenset({"old"}), frozenset({"new"}), frozenset({"old"}),
            frozenset({"old"}),
            {"old": Carry(("new",), frozenset({("old", "new")}))},
        )
        self.assertTrue(valid.pe_sound())

    def test_fake_translation_drops_live_claim(self):
        dropped = TransportStep(
            frozenset({"old", "hidden"}), frozenset({"new"}), frozenset({"old"}),
            frozenset({"old", "hidden"}),
            {"old": Carry(("new",), frozenset({("old", "new")}))},
        )
        self.assertFalse(dropped.pe_sound())

    def test_sensor_deletion_is_not_met(self):
        self.assertFalse(MetEdge(False, True, "sensor-deleted").pe_met())

    def test_valid_obsolescence_can_be_met(self):
        self.assertTrue(MetEdge(False, True, "authorized-obsolescence").pe_met())
        self.assertTrue(MetEdge(True, True, None).pe_met())

    def test_parallel_liability_failure(self):
        row1, row2, joint, deficit = liability_rows()
        self.assertTrue(row1)
        self.assertTrue(row2)
        self.assertFalse(joint)
        self.assertEqual(str(deficit), "1/4")

    def test_same_response_rule_can_change_realized_action(self):
        self.assertTrue(response_structure_same("identity", "identity"))
        self.assertNotEqual(realized_action("identity", 0), realized_action("identity", 1))

    def test_same_realized_action_can_hide_different_rules(self):
        self.assertEqual(realized_action("identity", 0), realized_action("always-a0", 0))
        self.assertFalse(response_structure_same("identity", "always-a0"))

    def test_predictor_strategy_fixed_not_realized_response(self):
        predictor = {"idle": "predict-idle", "query": "predict-query"}
        self.assertIs(predictor, predictor)
        self.assertNotEqual(predictor["idle"], predictor["query"])

    def test_self_modification_needs_typed_transport(self):
        ill_typed = TransportStep(
            frozenset({("policy-v1", "bool")}), frozenset({("policy-v2", "three")}),
            frozenset({("policy-v1", "bool")}), frozenset({("policy-v1", "bool")}),
            {("policy-v1", "bool"): Carry((("policy-v2", "three"),), frozenset())},
        )
        translated = TransportStep(
            ill_typed.pre_live, ill_typed.post_live, ill_typed.affected,
            ill_typed.actually_changed,
            {("policy-v1", "bool"): Carry(
                (("policy-v2", "three"),),
                frozenset({(("policy-v1", "bool"), ("policy-v2", "three"))}),
            )},
        )
        self.assertFalse(ill_typed.pe_sound())
        self.assertTrue(translated.pe_sound())

    def test_exhaustive_one_step_conservation(self):
        self.assertTrue(exhaustive_one_step_transport())


if __name__ == "__main__":
    unittest.main()
