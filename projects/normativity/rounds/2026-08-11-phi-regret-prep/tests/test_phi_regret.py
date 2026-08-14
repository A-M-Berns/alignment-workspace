"""The verdicts the thirteen experiments are supposed to produce.

Each test asserts an exact number or an exact obstruction code. A test that
asserted only "the comparator did better" would be the collapse this whole
substrate exists to prevent, so nothing here compares a single boolean.
"""

from __future__ import annotations

import unittest
from fractions import Fraction as Q

from src import experiments as ex
from src.certificates import (
    ADMITTED,
    CERTIFIER_FOOTPRINT,
    REJECTED,
    UNRESOLVED,
    LawfulEditCertificate,
    check,
)
from src.model import (
    BASIS_DECLINE,
    BASIS_MERITS,
    FootprintViolation,
    PrefixReader,
    reader_at,
    response_for,
)
from src.regret import evaluate, evaluate_class, locality, pattern_of
from src.replay import (
    FILINGS_ENDOGENOUS,
    FILINGS_FROZEN,
    actual_run,
    faithful,
    replay,
)


def run(experiment: ex.Experiment):
    return evaluate_class(experiment.history, experiment.comparators,
                          policy=experiment.policy, filings=experiment.filings)


def result(experiment: ex.Experiment, phi_id: str):
    report = run(experiment)
    return next(r for r in report.results if r.phi_id == phi_id)


class Substrate(unittest.TestCase):
    """S0: every history is well formed and replaying the identity reproduces it."""

    def test_every_history_is_well_formed(self):
        for build in ex.ALL:
            experiment = build()
            with self.subTest(experiment.label):
                self.assertEqual(experiment.history.well_formed(), [])

    def test_identity_replay_reproduces_the_actual_run(self):
        for build in ex.ALL:
            experiment = build()
            with self.subTest(experiment.label):
                base = actual_run(experiment.history, policy=experiment.policy,
                                  filings=experiment.filings)
                self.assertTrue(faithful(experiment.history, base))

    def test_replay_is_deterministic(self):
        for build in ex.ALL:
            experiment = build()
            for phi in experiment.comparators:
                with self.subTest(f"{experiment.label}/{phi.phi_id}"):
                    first = replay(experiment.history, phi, policy=experiment.policy,
                                   filings=experiment.filings)
                    second = replay(experiment.history, phi, policy=experiment.policy,
                                    filings=experiment.filings)
                    self.assertEqual(first.outcomes, second.outcomes)
                    self.assertEqual(first.total_charge, second.total_charge)

    def test_the_certifier_cannot_read_the_charge_table(self):
        """No-cost-laundering is structural: the table is not in the declaration."""
        self.assertNotIn("charges", CERTIFIER_FOOTPRINT)
        experiment = ex.e3_lawful_one_shot()
        reader = reader_at(experiment.history, 1, CERTIFIER_FOOTPRINT)
        with self.assertRaises(FootprintViolation):
            reader._read("charges")  # noqa: SLF001 — exercising the declaration

    def test_a_guard_that_reaches_for_the_charge_table_raises(self):
        """The declaration is a precondition on the run, not a report about it.

        A guard selecting edits by what they save is the failure the footprint
        exists to prevent, and it fails loudly rather than quietly succeeding.
        """
        from src.replay import Comparator

        def greedy(reader: PrefixReader, occ, actual) -> bool:
            reader._read("charges")  # noqa: SLF001 — the thing being refused
            return True

        experiment = ex.e3_lawful_one_shot()
        phi = Comparator("phi:greedy", greedy, lambda r, o, a: None)
        with self.assertRaises(FootprintViolation):
            replay(experiment.history, phi)

    def test_sign_convention(self):
        """Positive regret means the learner paid more than the comparator."""
        experiment = ex.e3_lawful_one_shot()
        outcome = result(experiment, "phi:e3")
        self.assertGreater(outcome.actual_charge, outcome.replay_charge)
        self.assertEqual(outcome.regret,
                         outcome.actual_charge - outcome.replay_charge)
        self.assertGreater(outcome.regret, 0)


class Legality(unittest.TestCase):

    def test_e1_profitable_but_unlawful(self):
        experiment = ex.e1_profitable_but_unlawful()
        outcome = result(experiment, "phi:e1")
        self.assertEqual(outcome.firings, ())
        self.assertEqual(outcome.rejections,
                         (("o:1", "certificate.replacement_unsupported"),))
        self.assertEqual(outcome.regret, Q(0))
        # The edit it refused would have been worth exactly one declined occasion.
        self.assertEqual(outcome.actual_charge, 4 * ex.DECLINE_CHARGE)

    def test_e2_successor_ratification(self):
        experiment = ex.e2_successor_ratification()
        later = result(experiment, "phi:e2-later")
        endorsed = result(experiment, "phi:e2-endorsed")
        self.assertEqual(later.rejections,
                         (("o:1", "certificate.not_historically_available"),))
        self.assertEqual(endorsed.rejections,
                         (("o:1", "certificate.successor_ratification"),))
        self.assertEqual(later.regret, Q(0))
        self.assertEqual(endorsed.regret, Q(0))

    def test_e6_magnitude_overreach(self):
        experiment = ex.e6_magnitude()
        within = result(experiment, "phi:e6-within")
        beyond = result(experiment, "phi:e6-beyond")
        self.assertEqual(within.firings, ("o:1",))
        self.assertEqual(within.regret, Q(1))
        self.assertEqual(beyond.firings, ())
        self.assertEqual(beyond.rejections,
                         (("o:1", "certificate.magnitude_unresolved"),))

    def test_e6_overreach_is_unresolved_not_rejected(self):
        """The magnitude predicate declines to rule rather than ruling against."""
        experiment = ex.e6_magnitude()
        history = experiment.history
        occasion = history.base_occasions[1]
        certificate = LawfulEditCertificate(
            "edit:probe", "o:1", 1, response_for(occasion, BASIS_DECLINE),
            response_for(occasion, BASIS_DECLINE, tolled=4), ("r:imped:1",),
            "auth:review")
        verdict = check(certificate, reader_at(history, 1, CERTIFIER_FOOTPRINT))
        self.assertEqual(verdict.status, UNRESOLVED)

    def test_e7_defeated_reason(self):
        experiment = ex.e7_defeated()
        outcome = result(experiment, "phi:e7")
        self.assertEqual(outcome.firings, ("o:early",))
        self.assertEqual(outcome.rejections,
                         (("o:late", "certificate.defeated_ground"),))
        self.assertEqual(outcome.regret, Q(1))

    def test_e8_burden_laundering(self):
        experiment = ex.e8_burden_laundering()
        erase = result(experiment, "phi:e8-erase")
        annex = result(experiment, "phi:e8-annex")
        self.assertEqual(erase.rejections, (("o:1", "burden.dropped"),))
        self.assertEqual(annex.rejections, (("o:1", "burden.foreign_closure"),))
        self.assertEqual(erase.regret, Q(0))
        self.assertEqual(annex.regret, Q(0))

    def test_striking_an_obligation_would_have_paid(self):
        """The laundering witness is only a witness if laundering was profitable."""
        experiment = ex.e8_burden_laundering()
        history = experiment.history
        from src.model import LedgerEffect, Response
        from src.replay import charge_of
        occasion = history.base_occasions[1]
        honest = response_for(occasion, BASIS_DECLINE)
        laundered = Response(BASIS_DECLINE, None, 0, LedgerEffect(drops=("d:o:1",)))
        self.assertEqual(charge_of(occasion, honest), ex.DECLINE_CHARGE)
        self.assertEqual(charge_of(occasion, laundered), Q(0))


class Advantage(unittest.TestCase):

    def test_e3_lawful_one_shot(self):
        experiment = ex.e3_lawful_one_shot()
        outcome = result(experiment, "phi:e3")
        self.assertEqual(outcome.firings, ("o:1",))
        self.assertEqual(outcome.regret, ex.DECLINE_CHARGE)
        base = actual_run(experiment.history)
        moved = [o.occasion_id for o in outcome.run.outcomes
                 if o.charge != base.charge_at(o.occasion_id)]
        self.assertEqual(moved, ["o:1"])

    def test_e4_recurrent_advantage_is_linear(self):
        for horizon in (12, 24, 48):
            experiment = ex.e4_recurrent(horizon=horizon, stride=3)
            outcome = result(experiment, "phi:e4")
            firings = len(range(0, horizon, 3))
            with self.subTest(horizon=horizon):
                self.assertEqual(outcome.fired, firings)
                self.assertEqual(outcome.regret, firings * ex.DECLINE_CHARGE)
                self.assertEqual(outcome.regret / horizon, Q(2, 3))

    def test_e4_is_a_remediable_pattern_with_a_uniform_saving(self):
        experiment = ex.e4_recurrent(horizon=24, stride=3)
        outcome = result(experiment, "phi:e4")
        recognised = [f"o:{i}" for i in range(0, 24, 3)]
        pattern = pattern_of(experiment.history, outcome, recognised, "pat:e4")
        self.assertEqual(pattern.firings, 8)
        self.assertEqual(pattern.uniform_saving, ex.DECLINE_CHARGE)
        self.assertEqual(pattern.rate, Q(1))
        self.assertEqual(pattern.total_saving, Q(16))

    def test_e5_non_recurrent_advantage_is_constant(self):
        constants = []
        for horizon in (12, 24, 48):
            experiment = ex.e5_non_recurrent(horizon=horizon, occurrences=4)
            outcome = result(experiment, "phi:e5")
            constants.append(outcome.regret)
        self.assertEqual(constants, [Q(8), Q(8), Q(8)])
        report = run(ex.e5_non_recurrent(horizon=48, occurrences=4))
        self.assertEqual(report.normalized(), Q(8, 48))


class Semantics(unittest.TestCase):

    def test_e9_fenced_locality_bound(self):
        for horizon in (12, 24):
            experiment = ex.e9_fenced_locality(horizon=horizon)
            outcome = result(experiment, "phi:withdraw")
            check_ = locality(experiment.history, outcome)
            with self.subTest(horizon=horizon):
                self.assertEqual(abs(check_.divergence), ex.DECLINE_CHARGE)
                self.assertEqual(check_.bound, ex.DECLINE_CHARGE)
                self.assertTrue(check_.untouched_identical)
                self.assertTrue(check_.holds)

    def test_e10_pooled_divergence_grows_with_the_horizon(self):
        seen = {}
        for horizon in (12, 24):
            experiment = ex.e10_pooled_divergence(horizon=horizon)
            outcome = result(experiment, "phi:withdraw")
            seen[horizon] = outcome.replay_charge - outcome.actual_charge
        self.assertEqual(seen[12], Q(24))
        self.assertEqual(seen[24], Q(48))
        self.assertEqual(seen[24], 2 * seen[12])

    def test_e10b_fencing_alone_gives_a_horizon_sized_bound(self):
        for horizon in (12, 24):
            experiment = ex.e10b_fenced_but_shared(horizon=horizon)
            outcome = result(experiment, "phi:withdraw")
            check_ = locality(experiment.history, outcome)
            with self.subTest(horizon=horizon):
                self.assertEqual(abs(check_.divergence), 2 * horizon)
                self.assertEqual(check_.bound, 2 * horizon)
                self.assertTrue(check_.holds)

    def test_e10c_without_the_coupling_divergence_is_the_edit(self):
        for horizon in (12, 24):
            experiment = ex.e10c_no_solvency_coupling(horizon=horizon)
            outcome = result(experiment, "phi:withdraw")
            with self.subTest(horizon=horizon):
                self.assertEqual(outcome.replay_charge - outcome.actual_charge,
                                 ex.DECLINE_CHARGE)

    def test_e11_guard_convention_changes_the_fire_set(self):
        experiment = ex.e11_guard_convention()
        on_actual = result(experiment, "phi:e11-actual")
        on_replay = result(experiment, "phi:e11-replay")
        self.assertEqual(on_actual.firings, ("o:0", "o:1", "o:2"))
        self.assertEqual(on_replay.firings, ("o:0", "o:2"))
        self.assertEqual(on_actual.regret, Q(6))
        self.assertEqual(on_replay.regret, Q(4))

    def test_e12_freezing_filings_undercounts_the_advantage(self):
        experiment = ex.e12_frozen_filings()
        frozen = evaluate(experiment.history, experiment.comparators[0],
                          filings=FILINGS_FROZEN)
        endogenous = evaluate(experiment.history, experiment.comparators[0],
                              filings=FILINGS_ENDOGENOUS)
        self.assertEqual(frozen.actual_charge, Q(8))
        self.assertEqual(endogenous.actual_charge, Q(8))
        self.assertEqual(frozen.regret, Q(2))
        self.assertEqual(endogenous.regret, Q(8))


class Feasibility(unittest.TestCase):

    def test_e13_an_unaffordable_lawful_comparator_is_inadmissible(self):
        experiment = ex.e13_resource_infeasible()
        report = run(experiment)
        every = next(r for r in report.results if r.phi_id == "phi:e13-all")
        two = next(r for r in report.results if r.phi_id == "phi:e13-two")
        self.assertEqual(every.fired, 3)
        self.assertFalse(every.admissible)
        self.assertEqual(every.regret, Q(6))
        self.assertTrue(two.admissible)
        self.assertEqual(two.regret, Q(4))
        # The supremum ranges over admissible comparators only, and the
        # unaffordable one's larger advantage does not enter it.
        self.assertEqual(report.sup_regret, Q(4))

    def test_feasibility_is_not_netted_into_the_charge(self):
        experiment = ex.e13_resource_infeasible()
        every = result(experiment, "phi:e13-all")
        self.assertEqual(every.replay_charge, Q(0))
        self.assertNotEqual(every.inadmissible_because, "")


if __name__ == "__main__":
    unittest.main()
