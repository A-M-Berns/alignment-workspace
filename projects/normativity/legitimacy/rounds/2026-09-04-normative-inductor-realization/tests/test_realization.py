from fractions import Fraction as F
import unittest

from src.realization import (
    Edge,
    affine_compose,
    approximate_argmax_regret,
    belief_only_response_counterexample,
    incompatible_reason_regions,
    normalized_euclidean_padding_profile,
    old_service_amplification,
    progress_certificate,
    projection_value_counterexample,
    sup_projection_padding_profile,
)


class RealizationTests(unittest.TestCase):
    def test_affine_transport_composition_and_exact_carry(self):
        self.assertEqual(affine_compose((F(3), F(1, 7)), (F(2), F(1, 5))),
                         (F(6), F(26, 35)))
        self.assertEqual(affine_compose((F(1), F(0)), (F(2), F(1, 5))),
                         (F(2), F(1, 5)))

    def test_approximate_argmax_value_bridge(self):
        displayed = {"investigate": F(3, 5), "ignore": F(1, 2)}
        certified = {"investigate": F(1, 2), "ignore": F(11, 20)}
        regret, bound = approximate_argmax_regret(
            displayed, certified, "investigate", F(0)
        )
        self.assertEqual(regret, F(1, 20))
        self.assertEqual(bound, F(1, 5))
        self.assertLessEqual(regret, bound)

    def test_argmax_factor_two_is_attained(self):
        # The displayed values tie, while the two calibration errors point in
        # opposite directions.  Either displayed argmax is legal.
        regret, bound = approximate_argmax_regret(
            {"best": F(1, 2), "chosen": F(1, 2)},
            {"best": F(3, 5), "chosen": F(2, 5)},
            "chosen",
            F(0),
        )
        self.assertEqual(regret, F(1, 5))
        self.assertEqual(regret, bound)

    def test_contract_progress_algebra_with_shared_service(self):
        prog, epsbar, residual, rhs = progress_certificate(
            exposure_mass={"e1": F(1, 2), "e2": F(1, 2)},
            service_weight={"s": F(1)},
            defect={"s": F(1, 10)},
            edges=[
                Edge("e1", "s", F(1, 2), F(2), F(1, 100)),
                Edge("e2", "s", F(1, 4), F(1), F(1, 50)),
            ],
            gamma=F(5, 4),
            loss_bound=F(1),
        )
        self.assertEqual(epsbar, F(1, 100))
        self.assertEqual(residual, F(1, 4))
        self.assertEqual(prog, F(77, 200))
        self.assertEqual(rhs, F(77, 200))

    def test_belief_only_does_not_entail_response(self):
        witness = belief_only_response_counterexample()
        self.assertEqual(witness["operative_defect"], 0)
        self.assertEqual(witness["chosen_action_loss"], 1)
        self.assertEqual(witness["required_additive_error"], 1)

    def test_old_normalization_is_not_padding_invariant(self):
        witness = normalized_euclidean_padding_profile(F(1, 4), 1, 3, F(2))
        self.assertEqual(witness["defect_squared_before"], F(1, 4))
        self.assertEqual(witness["defect_squared_after"], F(1, 16))
        self.assertEqual(witness["service_before"], F(2))
        self.assertEqual(witness["service_after"], F(8))
        self.assertEqual(witness["projection_work"], F(1, 2))

    def test_sup_defect_and_lambda_service_ignore_harmless_padding(self):
        witness = sup_projection_padding_profile([F(1, 2), F(-1, 4)], 7, F(3))
        self.assertEqual(witness["defect_before"], witness["defect_after"])
        self.assertEqual(witness["service_before"], witness["service_after"])

    def test_projection_admissibility_is_not_value_truth(self):
        witness = projection_value_counterexample()
        self.assertEqual(witness["distance_to_region"], 0)
        self.assertEqual(witness["chosen_regret"], 1)

    def test_old_service_hypotheses_imply_new_gamma_column_bound(self):
        load, bound = old_service_amplification(
            column_mass=F(3), weighted_column=F(6), service_mass=F(4),
            total_claim=F(10), total_service=F(5), old_lipschitz=F(2),
            parsimony=F(1, 2),
        )
        self.assertEqual(load, F(3, 5))
        self.assertEqual(bound, F(4, 5))
        self.assertLessEqual(load, bound)

    def test_individually_feasible_reasons_can_conflict_jointly(self):
        self.assertFalse(incompatible_reason_regions(F(1, 10)))


if __name__ == "__main__":
    unittest.main()
