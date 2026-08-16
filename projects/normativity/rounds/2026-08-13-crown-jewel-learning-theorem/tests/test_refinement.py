"""The refinement pass: the corrections, and the controls K1-K10."""
from __future__ import annotations

import inspect
import unittest
from fractions import Fraction
from random import Random

import integration
from actual import loaded_start, loss_vector, replenishing
from competing import (
    ACTIONS,
    COMPETING,
    INCOHERENT,
    ONE_WAY,
    active_rules,
    both_certificates_hold,
)
from dynamics import edges, is_transient, zero_mass_actions
from fixture import C, H, U
from learning import ACKNOWLEDGE, HOLD, LAMBDA, public_status, step
from moves import Move, apply_move
from schedules import exposure_count, sparse
from stochastic import (
    SampledRun,
    compensator_gap,
    expected_counts,
    sampled_run,
)


def both_active_state():
    """A public state where both competing certificates hold."""
    state = apply_move(loaded_start(), Move("assert", H, content=U))
    return replenishing(state, C, H)


class K3IndependentlyJustifiedReturnRoute(unittest.TestCase):
    """The correction. A return route need not be an anti-repair."""

    def test_both_certificates_hold_in_one_public_state(self):
        status = public_status(both_active_state(), H, C)
        self.assertTrue(status.has_unacknowledged)
        self.assertTrue(status.has_defeated_acknowledgment)
        self.assertTrue(both_certificates_hold(status))

    def test_the_two_edges_carry_different_certificates(self):
        certificates = {edge.certificate for edge in COMPETING}
        self.assertEqual(len(certificates), len(COMPETING))
        self.assertNotIn("none", certificates)

    def test_a_one_way_class_leaves_the_target_transient(self):
        status = public_status(both_active_state(), H, C)
        rules = active_rules(ONE_WAY, status)
        self.assertTrue(is_transient(edges(rules, ACTIONS), HOLD))
        self.assertEqual(zero_mass_actions(rules, ACTIONS), frozenset({HOLD}))

    def test_but_competing_legitimate_reasons_make_it_recurrent(self):
        # The claim withdrawn from the first pass. The return route here is
        # licensed by a *different* certificate, and each edge stands on its own.
        status = public_status(both_active_state(), H, C)
        rules = active_rules(COMPETING, status)
        self.assertFalse(is_transient(edges(rules, ACTIONS), HOLD))
        self.assertEqual(zero_mass_actions(rules, ACTIONS), frozenset())

    def test_the_incoherent_class_does_the_same_thing_for_a_worse_reason(self):
        # Both classes make the target recurrent, so recurrence alone is no
        # evidence of incoherence — which is exactly why the first pass's
        # inference was invalid.
        status = public_status(both_active_state(), H, C)
        for cls in (INCOHERENT, COMPETING):
            rules = active_rules(cls, status)
            self.assertFalse(is_transient(edges(rules, ACTIONS), HOLD))


class K8TheGraphConditionIsWhatSurvives(unittest.TestCase):
    """Transience is the theorem; coherence is not."""

    def test_transience_is_stated_over_the_active_graph_alone(self):
        source = inspect.getsource(is_transient)
        self.assertNotIn("certificate", source)
        self.assertNotIn("coherent", source)

    def test_and_it_decides_zero_mass(self):
        status = public_status(both_active_state(), H, C)
        for cls, expected in ((ONE_WAY, frozenset({HOLD})), (COMPETING, frozenset())):
            self.assertEqual(zero_mass_actions(active_rules(cls, status), ACTIONS), expected)


class K4FullGraphDependence(unittest.TestCase):
    """Per-repair bounds are modular; learner dynamics are not."""

    def test_adding_a_competing_repair_changes_the_targets_status(self):
        status = public_status(both_active_state(), H, C)
        without = zero_mass_actions(active_rules(ONE_WAY, status), ACTIONS)
        with_extra = zero_mass_actions(active_rules(COMPETING, status), ACTIONS)
        self.assertIn(HOLD, without)
        self.assertNotIn(HOLD, with_extra)

    def test_which_is_a_dynamics_fact_not_a_bound_fact(self):
        # The surgical inequality for the first repair reads only that repair's
        # map, so adding the second cannot change it. The learner's distribution
        # is a different matter, and the test above shows it changes.
        first = ONE_WAY[0]
        self.assertEqual(first.source, HOLD)
        self.assertEqual(first.target, ACKNOWLEDGE)


class K1StochasticRegister(unittest.TestCase):
    """`Q_T` is random under sampling, so the expectation must be on both sides."""

    def test_trajectories_differ_under_genuine_sampling(self):
        runs = [sampled_run(seed, horizon=10) for seed in range(6)]
        masses = {run.bad_mass for run in runs}
        counts = {run.bad_count for run in runs}
        self.assertGreater(len(masses | counts), 1)

    def test_the_correct_identity_is_between_expectations(self):
        # `E[N_T] = E[Q_T]`, not `E[N_T] = Q_T`: the right-hand side is itself a
        # random variable once the state depends on the sampled action.
        runs = [sampled_run(seed, horizon=10) for seed in range(200)]
        mean_count, mean_mass = expected_counts(runs)
        self.assertLess(abs(mean_count - mean_mass), Fraction(1, 5))

    def test_the_difference_is_a_compensated_sum(self):
        # `N_T - Q_T` is a sum of per-date differences each with conditional mean
        # zero, so the empirical average of the gap is near zero and is not
        # systematically signed.
        runs = [sampled_run(seed, horizon=10) for seed in range(200)]
        gap = compensator_gap(runs)
        self.assertLess(abs(gap), Fraction(1, 5))


class K2InformationTiming(unittest.TestCase):
    """The learner commits `p_t` before consuming `ell_t`."""

    def test_the_distribution_is_prepared_before_the_update(self):
        source = inspect.getsource(integration.run_learner)
        prepare_at = source.index("engine.prepare")
        distribution_at = source.index("prepared.distribution")
        update_at = source.index("engine.update")
        self.assertLess(prepare_at, distribution_at)
        self.assertLess(distribution_at, update_at)

    def test_prepare_is_not_given_the_loss_vector(self):
        signature = inspect.signature(integration.BlumMansourLearner.prepare)
        self.assertEqual(list(signature.parameters), ["self", "maps"])

    def test_determination_and_observability_come_apart(self):
        # `ell_t` is a function of `S_t` and so is determined when the date opens
        # — but the learner's choice does not read it. Both facts, stated
        # separately, are what "prospective" has to mean.
        state = both_active_state()
        self.assertEqual(loss_vector(state, H, C), loss_vector(state, H, C))
        signature = inspect.signature(integration.BlumMansourLearner.update)
        self.assertIn("charge_loss", signature.parameters)


class K5CoverageAtTheRegretScale(unittest.TestCase):
    """The square-root boundary witness, retained."""

    def test_sparse_exposure_sits_at_the_regret_scale(self):
        self.assertEqual(
            [exposure_count(sparse, t) for t in (16, 64, 256, 1024)], [4, 8, 16, 32]
        )


class K10NoHiddenCorrectness(unittest.TestCase):
    """No hypothesis refers to a hidden true norm."""

    def test_no_certificate_names_a_truth_predicate(self):
        for edge in COMPETING + INCOHERENT + ONE_WAY:
            for banned in ("true", "correct", "actual", "objective", "oracle"):
                self.assertNotIn(banned, edge.certificate)

    def test_the_state_still_carries_no_oracle_field(self):
        state = both_active_state()
        for banned in ("true_score", "actual_adequacy", "objective_norm"):
            self.assertNotIn(banned, set(vars(state)))


if __name__ == "__main__":
    unittest.main()
