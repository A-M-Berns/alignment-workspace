import unittest
from itertools import product

from audit_models import LOCALITY_MODELS, NcssStep, REGISTRATION_TRACE, exact_ncss


class LocalityAudit(unittest.TestCase):
    def test_nine_complete_locality_examples(self):
        self.assertEqual(len(LOCALITY_MODELS), 9)
        self.assertTrue(all(m.cfp_holds() for m in LOCALITY_MODELS.values()))

    def test_cfp_and_rp_admit_whole_agent_replacement(self):
        whole = LOCALITY_MODELS["whole_agent_replacement"]
        fake = LOCALITY_MODELS["fake_rp"]
        self.assertTrue(whole.rp_holds())
        self.assertFalse(whole.behaviorally_local())
        self.assertTrue(fake.rp_holds())
        self.assertFalse(fake.behaviorally_local())

    def test_extensional_locality_survives_reactive_exteriors(self):
        for name in (
            "extensional_local",
            "predictor_local",
            "strategic_local",
            "self_modify_local",
        ):
            self.assertTrue(LOCALITY_MODELS[name].behaviorally_local(), name)

    def test_delegation_location_changes_verdict(self):
        self.assertFalse(LOCALITY_MODELS["delegation_query_factor"].behaviorally_local())
        self.assertTrue(LOCALITY_MODELS["delegation_residual_factor"].behaviorally_local())

    def test_no_nontrivial_patch(self):
        model = LOCALITY_MODELS["no_nontrivial_patch"]
        self.assertFalse(model.behaviorally_local())

    def test_nonconstant_residual_observation_can_be_preserved(self):
        model = LOCALITY_MODELS["extensional_local"]
        self.assertTrue(model.residual_observation_nontrivial())
        self.assertTrue(model.behaviorally_local())


class NcssAudit(unittest.TestCase):
    def test_corrected_ncss_exhaustive(self):
        for values in product((False, True), repeat=6):
            step = NcssStep(*values)
            self.assertTrue(exact_ncss(step), values)

    def test_relevance_loss_falsifies_pr71_inference_to_not_implements(self):
        obsolete = NcssStep(True, False, False, False, False, False)
        self.assertTrue(obsolete.post_live)
        self.assertTrue(obsolete.post_implements)

    def test_each_load_bearing_hypothesis_has_a_countermodel(self):
        sound = NcssStep(True, True, False, False, False, False)
        self.assertTrue(sound.post_live)
        self.assertFalse(sound.post_implements)

        no_pre_live = NcssStep(False, True, False, False, False, False)
        self.assertFalse(no_pre_live.post_live)

        no_post_active = NcssStep(True, False, False, False, False, False)
        self.assertTrue(no_post_active.post_implements)

        represented = NcssStep(True, True, True, False, False, False)
        self.assertTrue(represented.post_implements)

        replacement_route = NcssStep(True, True, False, True, False, False)
        self.assertTrue(replacement_route.post_implements)

        unsound_close = NcssStep(True, True, False, False, True, False)
        self.assertFalse(unsound_close.local_close_adequacy)
        self.assertFalse(unsound_close.post_live)

        silent_drop = NcssStep(True, True, False, False, False, False, False, True)
        self.assertTrue(silent_drop.local_close_adequacy)
        self.assertFalse(silent_drop.post_live)

        nonfresh_successor = NcssStep(True, True, False, False, True, True, True, False)
        self.assertTrue(nonfresh_successor.local_close_adequacy)
        self.assertFalse(nonfresh_successor.post_live)

    def test_four_registration_stages_are_distinct(self):
        self.assertEqual(len(set(REGISTRATION_TRACE)), 4)
        for stage in REGISTRATION_TRACE:
            self.assertTrue(stage.capable)
            self.assertFalse(stage.registered and not stage.receipt)
            self.assertFalse(stage.receipt and not stage.exercised)


if __name__ == "__main__":
    unittest.main()
