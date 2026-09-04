from fractions import Fraction as F
import unittest

from src.realization import (
    Edge,
    affine_compose,
    approximate_argmax_regret,
    belief_only_response_counterexample,
    incompatible_reason_regions,
    progress_certificate,
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

    def test_individually_feasible_reasons_can_conflict_jointly(self):
        self.assertFalse(incompatible_reason_regions(F(1, 10)))


if __name__ == "__main__":
    unittest.main()
