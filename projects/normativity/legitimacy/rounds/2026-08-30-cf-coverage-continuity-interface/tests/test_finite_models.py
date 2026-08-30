import unittest
from itertools import product

from finite_models import EXPECTED, MODELS, signature
from self_sealing import Step, ncss


class FiniteModels(unittest.TestCase):
    def test_all_twenty_models_have_complete_beta_tables(self):
        self.assertEqual(len(MODELS), 20)
        for model in MODELS.values():
            self.assertEqual(
                set(model.beta),
                {(q, z) for q in model.queries for z in model.complements},
            )

    def test_classifications(self):
        self.assertEqual(set(MODELS), set(EXPECTED))
        for name, model in MODELS.items():
            self.assertEqual(signature(model), EXPECTED[name], name)

    def test_route_existence_does_not_imply_exercise(self):
        model = MODELS["route_never_exercised"]
        self.assertTrue(model.implemented())
        self.assertFalse(model.actual_registration())

    def test_exposure_does_not_imply_registration(self):
        model = MODELS["receipt_not_registered"]
        self.assertTrue(model.structurally_accessible())
        self.assertFalse(model.actual_registration())
        self.assertFalse(model.implemented())

    def test_target_change_rejects_end_to_end_route(self):
        for name in ("changes_target", "self_fulfilling"):
            model = MODELS[name]
            self.assertTrue(model.structurally_accessible())
            self.assertFalse(model.target_preserving())
            self.assertFalse(model.implemented())

    def test_ncss_boolean_skeleton_exhaustive(self):
        for values in product((False, True), repeat=5):
            self.assertTrue(ncss(Step(*values)), values)

    def test_continuity_alone_allows_clean_self_sealing(self):
        attack = Step(False, False, False, True, False)
        self.assertTrue(attack.defect)
        self.assertFalse(attack.next_live)
        self.assertFalse(attack.answerable_failure)
        self.assertFalse(attack.resolution_sound)


if __name__ == "__main__":
    unittest.main()
