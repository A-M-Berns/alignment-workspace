from __future__ import annotations

import sys
import unittest
from dataclasses import replace
from decimal import Context, Decimal, localcontext
from fractions import Fraction as Q
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PREP = ROOT.parent / "2026-08-11-phi-regret-prep"
APPLICABILITY = ROOT.parent / "2026-08-11-phi-regret-applicability"
BRIDGE = ROOT.parent / "2026-08-11-phi-regret-bridge"
sys.path[:0] = [str(ROOT / "src"), str(BRIDGE / "src"),
                str(APPLICABILITY / "src"), str(PREP)]

from experiment import (
    FAILURE_DELTA,
    HORIZONS,
    charge_vector,
    comparator_expected,
    impediment_pressure,
    integration_audit,
    maps_for,
    persistent_interval,
    recurrent_lower_bound,
    repository_expected_loss,
    run_fixture,
)
from phi_learner import (
    BlumMansourLearner,
    stationary_distribution,
    transition_from_weights,
)
from semantic_bridge import (
    AUDITED_PROGRAMS,
    LAMBDA,
    frozen_environment_violations,
    non_capture_audit,
)
from src.model import Accounting


class StationarySelection(unittest.TestCase):

    def test_identity_chain_selects_the_uniform_distribution(self):
        matrix = tuple(tuple(Q(int(i == j)) for j in range(4)) for i in range(4))
        self.assertEqual(stationary_distribution(matrix), (Q(1, 4),) * 4)

    def test_reducible_chain_uses_uniform_start_absorption_weights(self):
        matrix = ((Q(1), Q(0), Q(0)),
                  (Q(1), Q(0), Q(0)),
                  (Q(0), Q(0), Q(1)))
        self.assertEqual(stationary_distribution(matrix),
                         (Q(2, 3), Q(0), Q(1, 3)))

    def test_nonunique_selector_is_exactly_stationary(self):
        matrix = ((Q(1), Q(0), Q(0), Q(0)),
                  (Q(1, 2), Q(1, 2), Q(0), Q(0)),
                  (Q(0), Q(0), Q(1, 3), Q(2, 3)),
                  (Q(0), Q(0), Q(1, 4), Q(3, 4)))
        distribution = stationary_distribution(matrix)
        pushed = tuple(sum((distribution[i] * matrix[i][j]
                            for i in range(4)), Q(0)) for j in range(4))
        self.assertEqual(distribution, pushed)
        self.assertEqual(sum(distribution, Q(0)), Q(1))
        self.assertTrue(all(value >= 0 for value in distribution))

    def test_degenerate_zero_weight_row_is_rejected(self):
        maps = ((0, 1), (0, 1))
        with self.assertRaises(ValueError):
            transition_from_weights(((Decimal(1), Decimal(0)),
                                     (Decimal(1), Decimal(1))), maps)


class TheoremFaithfulState(unittest.TestCase):

    def test_state_has_eight_rows_and_seventy_two_weights(self):
        learner = BlumMansourLearner(12, 8, 9, loss_max=Q(2))
        self.assertEqual(len(learner.weights), 8)
        self.assertTrue(all(len(row) == 9 for row in learner.weights))
        self.assertEqual(learner.weight_count, 72)
        self.assertTrue(Decimal(0) < learner.beta < Decimal(1))

    def test_transition_and_stationarity_hold_after_updates(self):
        fixture = impediment_pressure(12)
        learner = BlumMansourLearner(12, 8, 9, loss_max=Q(2))
        for occasion in fixture.history.actual_occasions():
            maps = maps_for(fixture.history, occasion)
            prepared = learner.prepare(maps)
            self.assertEqual(sum(prepared.distribution, Q(0)), Q(1))
            pushed = tuple(sum((prepared.distribution[i]
                                * prepared.transition[i][j]
                                for i in range(8)), Q(0)) for j in range(8))
            self.assertEqual(pushed, prepared.distribution)
            learner.update(prepared, charge_vector(occasion))
            self.assertTrue(all(weight > 0 and weight.is_finite()
                                for row in learner.weights for weight in row))

    def test_precision_change_is_numerically_small_not_called_exact(self):
        low = next(run for run in run_fixture(impediment_pressure(24), precision=50)
                   if run.policy == "blum_mansour")
        high = next(run for run in run_fixture(impediment_pressure(24), precision=90)
                    if run.policy == "blum_mansour")
        with localcontext(Context(prec=45)):
            self.assertLess(abs(low.expected_charge - high.expected_charge),
                            Decimal("1e-40"))
            self.assertLess(abs(low.max_regret - high.max_regret),
                            Decimal("1e-40"))

    def test_learning_parameter_is_horizon_tuned(self):
        short = BlumMansourLearner(12, 8, 9, loss_max=Q(2))
        long = BlumMansourLearner(96, 8, 9, loss_max=Q(2))
        self.assertNotEqual(short.beta, long.beta)
        self.assertLess(short.beta, long.beta)


class FrozenExperiments(unittest.TestCase):

    def test_every_run_reports_the_complete_nine_program_class(self):
        expected_ids = {program.program_id for program in AUDITED_PROGRAMS}
        for builder in (persistent_interval, impediment_pressure):
            for horizon in HORIZONS:
                for run in run_fixture(builder(horizon)):
                    self.assertEqual(set(run.comparator_charge), expected_ids)
                    self.assertEqual(set(run.regret), expected_ids)
                    self.assertEqual(set(run.failure_mass), expected_ids)

    def test_uniform_policy_exhibits_linear_repair_regret(self):
        for horizon in HORIZONS:
            uniform = next(run for run in run_fixture(persistent_interval(horizon))
                           if run.policy == "uniform")
            self.assertEqual(uniform.regret["repair_declines"],
                             Decimal(horizon) / Decimal(4))
            self.assertEqual(uniform.max_regret,
                             uniform.regret["repair_declines"])

    def test_phi_learner_retires_the_persistent_interval_failure_mass(self):
        for horizon in HORIZONS:
            learner = next(run for run in run_fixture(persistent_interval(horizon))
                           if run.policy == "blum_mansour")
            self.assertEqual(learner.failure_mass["repair_declines"], Decimal(0))
            self.assertEqual(learner.regret["repair_declines"], Decimal(0))
            self.assertEqual(learner.max_regret, Decimal(0))

    def test_impediment_fixture_exercises_nontrivial_weight_learning(self):
        short = next(run for run in run_fixture(impediment_pressure(12))
                     if run.policy == "blum_mansour")
        long = next(run for run in run_fixture(impediment_pressure(96))
                    if run.policy == "blum_mansour")
        self.assertGreater(short.regret["toll_declines_4"], Decimal(0))
        self.assertGreater(long.regret["toll_declines_4"], short.regret["toll_declines_4"])
        self.assertLess(long.normalized_regret, short.normalized_regret)

    def test_numerical_regret_stays_below_the_source_proof_bound(self):
        for builder in (persistent_interval, impediment_pressure):
            for horizon in HORIZONS:
                learner = next(run for run in run_fixture(builder(horizon))
                               if run.policy == "blum_mansour")
                self.assertIsNotNone(learner.source_bound)
                self.assertLessEqual(learner.max_regret, learner.source_bound)

    def test_zero_phi_regret_need_not_minimize_charge(self):
        learner = next(run for run in run_fixture(persistent_interval(96))
                       if run.policy == "blum_mansour")
        hedge = next(run for run in run_fixture(persistent_interval(96))
                     if run.policy == "hedge_actions")
        self.assertEqual(learner.max_regret, Decimal(0))
        self.assertEqual(learner.expected_charge, Decimal(48))
        self.assertLess(hedge.expected_charge, learner.expected_charge)

    def test_recurrent_lower_bound_is_respected_on_the_uniform_witness(self):
        repair = next(program for program in AUDITED_PROGRAMS
                      if program.program_id == "repair_declines")
        for horizon in HORIZONS:
            uniform = next(run for run in run_fixture(persistent_interval(horizon))
                           if run.policy == "uniform")
            lower = recurrent_lower_bound(uniform, repair, FAILURE_DELTA)
            self.assertGreaterEqual(uniform.regret[repair.program_id], lower)
            self.assertEqual(lower, Decimal(horizon) / Decimal(16))

    def test_expected_label_charge_equals_decoded_repository_charge(self):
        fixture = impediment_pressure(12)
        learner = BlumMansourLearner(12, 8, 9, loss_max=Q(2))
        for occasion in fixture.history.actual_occasions():
            prepared = learner.prepare(maps_for(fixture.history, occasion))
            label_value = sum((prepared.distribution[index] * value
                               for index, value in enumerate(charge_vector(occasion))), Q(0))
            self.assertEqual(label_value,
                             repository_expected_loss(fixture.history, occasion,
                                                      prepared.distribution))
            for program_index in range(9):
                self.assertEqual(
                    comparator_expected(prepared.distribution,
                                        charge_vector(occasion),
                                        prepared.maps[program_index]),
                    sum((prepared.distribution[source]
                         * charge_vector(occasion)[prepared.maps[program_index][source]]
                         for source in range(8)), Q(0)))
            learner.update(prepared, charge_vector(occasion))


class IntegrationBoundary(unittest.TestCase):

    def test_sampled_responses_are_answerable_and_within_response_service(self):
        run = next(run for run in run_fixture(impediment_pressure(24))
                   if run.policy == "blum_mansour")
        audit = integration_audit(run)
        self.assertTrue(audit.well_formed_record)
        self.assertTrue(audit.identity_replay_faithful)
        self.assertTrue(audit.canonical_responses)
        self.assertTrue(audit.no_burden_erasure)
        self.assertTrue(audit.response_service_feasible)
        self.assertTrue(audit.legality_non_capture)

    def test_learning_computation_is_not_priced_by_the_service_model(self):
        run = next(run for run in run_fixture(impediment_pressure(12))
                   if run.policy == "blum_mansour")
        audit = integration_audit(run)
        self.assertFalse(audit.learning_computation_accounted)
        self.assertFalse(audit.integrated)

    def test_legality_boundary_remains_the_audited_finite_class(self):
        self.assertEqual(non_capture_audit(), ())

    def test_suspension_reopens_the_additive_loss_boundary(self):
        fixture = impediment_pressure(12)
        changed = replace(
            fixture.history,
            accounting=Accounting({}, suspends=True),
        )
        self.assertIn("solvency/suspension coupling is enabled",
                      frozen_environment_violations(changed))


if __name__ == "__main__":
    unittest.main()
