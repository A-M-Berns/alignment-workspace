from __future__ import annotations

import sys
import unittest
from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
PREP = HERE.parent / "2026-08-11-phi-regret-prep"
APPLICABILITY = HERE.parent / "2026-08-11-phi-regret-applicability"
sys.path[:0] = [str(HERE / "src"), str(APPLICABILITY / "src"), str(PREP)]

from online_interface import PaddedRound, available_actions, expected_loss, pushforward
from semantic_bridge import (
    AUDITED_PROGRAMS,
    LAMBDA,
    PROGRAM_DESCRIPTIONS,
    ProgramKind,
    SemanticAction,
    as_repository_comparator,
    canonical_responses,
    commuting_square_holds,
    compile_label_map,
    decode_action,
    encode_response,
    frozen_environment_violations,
    label_actual_loss,
    label_counterfactual_loss,
    label_loss,
    label_regret,
    non_capture_audit,
    recurrent_failure_lower_bound,
    repository_regret,
)
from src import experiments as ex
from src.certificates import PolicySuite
from src.model import Accounting, Response
from src.replay import charge_of, replay


def audit_history(horizon: int):
    occasions = [ex.occasion(i) for i in range(horizon)]
    responses = {
        occasion.occasion_id: decode_action(occasion, LAMBDA[i % len(LAMBDA)])
        for i, occasion in enumerate(occasions)
    }
    reasons = []
    for i in range(horizon):
        reasons.extend((ex.clearing_interval(i), ex.impediment(i, dates=4),
                        ex.ripeness(i)))
    return ex.history(f"h:bridge:{horizon}", occasions, responses, reasons,
                      horizon=horizon, accounting=Accounting({}, suspends=False))


class FixedAlphabet(unittest.TestCase):

    def test_lambda_has_exactly_eight_horizon_independent_labels(self):
        self.assertEqual(len(LAMBDA), 8)
        self.assertEqual(len(set(LAMBDA)), 8)
        for horizon in (12, 24, 48, 96):
            labels = {encode_response(occasion, response)
                      for occasion in audit_history(horizon).actual_occasions()
                      for response in canonical_responses(occasion)}
            self.assertEqual(labels, set(LAMBDA))

    def test_ledger_ids_are_introduced_only_by_decode(self):
        first, second = ex.occasion(0), ex.occasion(1)
        self.assertEqual(SemanticAction.MERITS_POSITIVE,
                         encode_response(first,
                                         decode_action(first, SemanticAction.MERITS_POSITIVE)))
        self.assertNotEqual(decode_action(first, SemanticAction.MERITS_POSITIVE),
                            decode_action(second, SemanticAction.MERITS_POSITIVE))
        self.assertNotIn("o:0", SemanticAction.MERITS_POSITIVE.value)
        self.assertNotIn("o:1", SemanticAction.MERITS_POSITIVE.value)

    def test_decode_is_a_bijection_onto_canonical_responses(self):
        for occasion in (ex.occasion(0), ex.occasion(91)):
            decoded = canonical_responses(occasion)
            self.assertEqual(len(set(decoded)), 8)
            self.assertEqual(set(decoded), set(available_actions(occasion)))
            for label in LAMBDA:
                self.assertIs(encode_response(occasion, decode_action(occasion, label)),
                              label)
            for response in decoded:
                self.assertEqual(decode_action(occasion,
                                               encode_response(occasion, response)),
                                 response)

    def test_noncanonical_ledger_effect_is_not_quotiented_away(self):
        occasion = ex.occasion(0)
        canonical = decode_action(occasion, SemanticAction.DEFAULT)
        noncanonical = replace(canonical, ledger=replace(canonical.ledger,
                                                         drops=("d:o:0",)))
        with self.assertRaises(ValueError):
            encode_response(occasion, noncanonical)

    def test_encode_decode_preserves_every_exact_charge(self):
        for horizon in (12, 24, 48, 96):
            for occasion in audit_history(horizon).actual_occasions():
                for label in LAMBDA:
                    response = decode_action(occasion, label)
                    self.assertEqual(label_loss(occasion, label),
                                     charge_of(occasion, response))
                    self.assertEqual(label_loss(occasion, label),
                                     label_loss(occasion,
                                                encode_response(occasion, response)))


class ComparatorFactorization(unittest.TestCase):

    def test_all_nine_programs_are_materialized_and_described(self):
        self.assertEqual(len(AUDITED_PROGRAMS), 9)
        self.assertEqual({program.program_id for program in AUDITED_PROGRAMS},
                         set(PROGRAM_DESCRIPTIONS))
        self.assertEqual(sum(program.kind is ProgramKind.TOLL_DECLINES
                             for program in AUDITED_PROGRAMS), 3)

    def test_every_program_factors_on_every_label_at_declared_horizons(self):
        for horizon in (12, 24, 48, 96):
            history = audit_history(horizon)
            for occasion in history.actual_occasions():
                for program in AUDITED_PROGRAMS:
                    with self.subTest(horizon=horizon,
                                      occasion=occasion.occasion_id,
                                      program=program.program_id):
                        self.assertTrue(commuting_square_holds(history, occasion,
                                                              program))

    def test_every_induced_map_is_total_and_closed_on_lambda(self):
        history = audit_history(12)
        for occasion in history.actual_occasions():
            for program in AUDITED_PROGRAMS:
                transform = compile_label_map(history, occasion, program)
                self.assertEqual(set(transform), set(LAMBDA))
                self.assertTrue(set(transform.values()) <= set(LAMBDA))

    def test_every_nonidentity_program_has_an_admitted_firing(self):
        history = audit_history(16)
        for program in AUDITED_PROGRAMS[1:]:
            changed = any(
                compile_label_map(history, occasion, program)[label] is not label
                for occasion in history.actual_occasions() for label in LAMBDA)
            with self.subTest(program=program.program_id):
                self.assertTrue(changed)

    def test_the_two_previously_missing_programs_have_admitted_witnesses(self):
        history = audit_history(12)
        decline_occ = history.actual_occasions()[3]
        merits_occ = history.actual_occasions()[0]
        default_rule = next(p for p in AUDITED_PROGRAMS
                            if p.kind is ProgramKind.DEFAULT_DECLINES)
        withdraw_rule = next(p for p in AUDITED_PROGRAMS
                             if p.kind is ProgramKind.WITHDRAW_MERITS)
        default_map = compile_label_map(history, decline_occ, default_rule)
        withdraw_map = compile_label_map(history, merits_occ, withdraw_rule)
        # Ripeness licenses the basis move, not erasure of an existing toll.
        self.assertIs(default_map[SemanticAction.DECLINE_0], SemanticAction.DEFAULT)
        self.assertIs(default_map[SemanticAction.DECLINE_3], SemanticAction.DECLINE_3)
        self.assertIs(withdraw_map[SemanticAction.MERITS_POSITIVE],
                      SemanticAction.DECLINE_0)

    def test_future_reason_cannot_fire_a_current_map(self):
        occasion = ex.occasion(0)
        future = ex.clearing_interval(0, filed_at=1)
        history = ex.history("h:future", [occasion],
                             {"o:0": decode_action(occasion,
                                                   SemanticAction.DECLINE_0)},
                             [future], horizon=2)
        repair = AUDITED_PROGRAMS[1]
        transform = compile_label_map(history, occasion, repair)
        self.assertEqual(transform, {label: label for label in LAMBDA})

    def test_interval_direction_selects_the_negative_merits_label(self):
        occasion = ex.occasion(0)
        negative = replace(ex.clearing_interval(0),
                           payload={"lower": Q(1, 5), "upper": Q(2, 5)})
        history = ex.history("h:negative", [occasion],
                             {"o:0": decode_action(occasion,
                                                   SemanticAction.DECLINE_0)},
                             [negative])
        transform = compile_label_map(history, occasion, AUDITED_PROGRAMS[1])
        self.assertIs(transform[SemanticAction.DECLINE_0],
                      SemanticAction.MERITS_NEGATIVE)
        self.assertTrue(commuting_square_holds(history, occasion,
                                               AUDITED_PROGRAMS[1]))

    def test_toll_four_is_identity_when_endpoint_support_is_unresolved(self):
        occasion = ex.occasion(0)
        history = ex.history("h:toll-limit", [occasion],
                             {"o:0": decode_action(occasion,
                                                   SemanticAction.DECLINE_0)},
                             [ex.impediment(0, dates=2)])
        toll_two = next(p for p in AUDITED_PROGRAMS
                        if p.program_id == "toll_declines_2")
        toll_four = next(p for p in AUDITED_PROGRAMS
                         if p.program_id == "toll_declines_4")
        self.assertIs(compile_label_map(history, occasion, toll_two)
                      [SemanticAction.DECLINE_0], SemanticAction.DECLINE_2)
        self.assertIs(compile_label_map(history, occasion, toll_four)
                      [SemanticAction.DECLINE_0], SemanticAction.DECLINE_0)


class PreservationAndBoundary(unittest.TestCase):

    def test_actual_and_counterfactual_charge_and_regret_are_preserved(self):
        for horizon in (12, 24, 48, 96):
            history = audit_history(horizon)
            identity_loss = replay(history,
                                   as_repository_comparator(AUDITED_PROGRAMS[0])).total_charge
            self.assertEqual(label_actual_loss(history), identity_loss)
            for program in AUDITED_PROGRAMS:
                repo_loss = replay(history, as_repository_comparator(program)).total_charge
                self.assertEqual(label_counterfactual_loss(history, program), repo_loss)
                self.assertEqual(label_regret(history, program),
                                 repository_regret(history, program))

    def test_pointwise_preservation_lifts_to_exact_expected_mixed_loss(self):
        history = audit_history(12)
        occasion = history.actual_occasions()[6]
        distribution = {label: Q(index + 1, 36)
                        for index, label in enumerate(LAMBDA)}
        loss = {label: label_loss(occasion, label) for label in LAMBDA}
        self.assertEqual(sum(distribution.values(), Q(0)), Q(1))
        for program in AUDITED_PROGRAMS:
            transform = compile_label_map(history, occasion, program)
            label_expected = expected_loss(pushforward(distribution, transform), loss)
            repo_expected = sum(
                (distribution[label]
                 * charge_of(occasion,
                             decode_action(occasion, transform[label])))
                for label in LAMBDA)
            self.assertEqual(label_expected, repo_expected)

    def test_every_theorem_facing_loss_is_bounded_by_two(self):
        history = audit_history(96)
        self.assertTrue(all(Q(0) <= label_loss(occasion, label) <= Q(2)
                            for occasion in history.actual_occasions()
                            for label in LAMBDA))

    def test_frozen_environment_boundary_is_explicit_and_executable(self):
        history = audit_history(12)
        self.assertEqual(frozen_environment_violations(history), ())
        coupled = replace(history, accounting=Accounting({"acct:main": Q(0)},
                                                         suspends=True))
        self.assertIn("solvency/suspension coupling is enabled",
                      frozen_environment_violations(coupled))
        first = history.base_occasions[0]
        altered = replace(first, schedule=replace(first.schedule, service_window=5))
        altered_history = replace(history,
                                  base_occasions=(altered,) + history.base_occasions[1:])
        self.assertIn("an occasion has a non-frozen service window",
                      frozen_environment_violations(altered_history))

    def test_raw_unavailable_padding_still_creates_artificial_regret(self):
        padded = PaddedRound(actions=("a", "b", "unavailable"),
                             available=frozenset(("a", "b")),
                             retract={"a": "a", "b": "b", "unavailable": "a"},
                             loss={"a": Q(1), "b": Q(2)})
        self.assertEqual(min(padded.loss.values()), Q(1))
        self.assertEqual(min((Q(1), Q(2), Q(0))), Q(0))
        self.assertEqual(padded.padded_loss("unavailable"), Q(1))

    def test_recurrent_failure_bound_is_exact(self):
        self.assertEqual(recurrent_failure_lower_bound(12, Q(2, 3), Q(1)), Q(7))
        self.assertEqual(recurrent_failure_lower_bound(Q(9, 2), Q(2), Q(1)), Q(8))


class NonCapture(unittest.TestCase):

    def test_the_declared_nine_and_default_policy_pass_finite_audit(self):
        self.assertEqual(non_capture_audit(), ())

    def test_a_policy_closing_over_an_occasion_fails_the_audit(self):
        captured = ex.occasion(0)

        def captured_bears_on(reason, coordinate, occasion):
            return (captured.schedule.refusal_tariff > 0
                    and coordinate in reason.licenses)

        policy = replace(PolicySuite(), bears_on=captured_bears_on)
        problems = non_capture_audit(policy=policy)
        self.assertTrue(any("policy suite differs" in problem for problem in problems))
        self.assertTrue(any("captures environment state" in problem
                            for problem in problems))


if __name__ == "__main__":
    unittest.main()
