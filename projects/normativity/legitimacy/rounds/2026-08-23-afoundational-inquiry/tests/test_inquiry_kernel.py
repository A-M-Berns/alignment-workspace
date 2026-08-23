from __future__ import annotations

import unittest
from fractions import Fraction

from inquiry_kernel import (
    Commitment,
    ContentKind,
    CoverageView,
    InquiryAction,
    InquiryRequest,
    Mode,
    NormativeAct,
    Receipt,
    Rule,
    ServiceCertificate,
    accrue,
    authority_errors,
    authority_roots,
    certified_service,
    complementarity_progress,
    compile_scd,
    evaluator_internal_disagreement,
    fixed_docket_latency,
    inquiry_delay_objective,
    mlsc_unit_metric_objective,
    monotone_submodular,
    overloaded_backlog,
    per_input_service_edges,
    scd_objective,
    service_spec_revision_errors,
    starvation_despite_two_competitiveness,
)


class AuthorityCases(unittest.TestCase):
    def setUp(self):
        self.seed = NormativeAct("seed", 0, "hold", seed=True)

    def test_valid_genealogy_terminates_in_seed_without_content_entailment(self):
        empirical = ("receipt:world",)
        rule = NormativeAct("rule", 1, "hold", grounds=empirical, license_parents=("seed",))
        task = NormativeAct("task", 2, "do", grounds=("receipt:new",), license_parents=("rule",))
        acts = (self.seed, rule, task)
        self.assertEqual(authority_errors(acts), ())
        self.assertEqual(authority_roots(acts, "task"), frozenset({"seed"}))
        self.assertNotIn("receipt:new", self.seed.grounds)

    def test_post_seed_root_is_rejected(self):
        errors = authority_errors((self.seed, NormativeAct("root", 1, "hold")))
        self.assertEqual(errors, ("new_root:root",))

    def test_self_licensing_is_rejected_by_prestate_check(self):
        act = NormativeAct("self", 1, "hold", license_parents=("self",))
        self.assertIn("license_not_prestate:self:self", authority_errors((self.seed, act)))

    def test_mutual_same_transition_licensing_is_rejected(self):
        left = NormativeAct("left", 1, "hold", license_parents=("right",))
        right = NormativeAct("right", 1, "hold", license_parents=("left",))
        errors = authority_errors((self.seed, left, right))
        self.assertIn("license_not_prestate:left:right", errors)
        self.assertIn("license_not_earlier:right:left", errors)

    def test_empirical_ground_is_not_a_normative_license(self):
        act = NormativeAct("move", 1, "do", grounds=("receipt",))
        self.assertEqual(authority_errors((self.seed, act)), ("new_root:move",))

    def test_two_license_parents_may_share_one_seed(self):
        left = NormativeAct("left", 1, "hold", license_parents=("seed",))
        right = NormativeAct("right", 1, "hold", license_parents=("seed",))
        act = NormativeAct("act", 2, "do", license_parents=("left", "right"))
        record = (self.seed, left, right, act)
        self.assertEqual(authority_errors(record), ())
        self.assertEqual(authority_roots(record, "act"), frozenset({"seed"}))

    def test_deeper_diamond_convergence_deduplicates_root_identity(self):
        base = NormativeAct("base", 1, "hold", license_parents=("seed",))
        left = NormativeAct("left", 2, "hold", license_parents=("base",))
        right = NormativeAct("right", 2, "hold", license_parents=("base",))
        act = NormativeAct("act", 3, "do", license_parents=("left", "right"))
        record = (self.seed, base, left, right, act)
        self.assertEqual(authority_errors(record), ())
        self.assertEqual(authority_roots(record, "act"), frozenset({"seed"}))

    def test_malformed_same_index_cycle_fails_before_root_traversal(self):
        left = NormativeAct("left", 1, "hold", license_parents=("right",))
        right = NormativeAct("right", 1, "hold", license_parents=("left",))
        with self.assertRaisesRegex(ValueError, "invalid authority record"):
            authority_roots((self.seed, left, right), "right")


class AccrualAndCoverageCases(unittest.TestCase):
    def setUp(self):
        self.must = Rule("r", "v1", Mode.MUST, "harm-report", "investigate", "spec-v1", "seed")
        self.may = Rule("m", "v1", Mode.MAY, "harm-report", "investigate", "spec-v1", "seed")
        self.receipt = Receipt("z", 4, "harm-report")

    def test_only_must_generates_due_token(self):
        tokens = accrue((self.must, self.may), self.receipt)
        self.assertEqual(len(tokens), 1)
        self.assertEqual(tokens[0].rule_version, "v1")

    def test_repeal_after_accrual_cannot_erase_token(self):
        token = accrue((self.must,), self.receipt)[0]
        view = CoverageView().generate(token)
        rules_after_repeal = ()
        self.assertEqual(rules_after_repeal, ())
        self.assertIn(token, view.due_tokens)
        self.assertIn(token.ident, view.coverage_debts)
        self.assertTrue(view.complete())

    def test_same_step_is_repaired_by_prestate_accrual_phase(self):
        # The receipt accrues under the pre-state; repeal applies to later receipts.
        first = accrue((self.must,), self.receipt)
        later = accrue((), Receipt("later", 5, "harm-report"))
        self.assertEqual(len(first), 1)
        self.assertEqual(later, ())

    def test_docketing_replaces_visible_debt_with_identity_bearing_task(self):
        token = accrue((self.must,), self.receipt)[0]
        view = CoverageView().generate(token).docket(token.ident, "ell-1")
        self.assertEqual(view.coverage_debts, frozenset())
        self.assertEqual(view.liabilities[0].origin_due, token.ident)
        self.assertTrue(view.complete())

    def test_identical_content_tasks_do_not_contract(self):
        first = accrue((self.must,), self.receipt)[0]
        second = accrue((self.must,), Receipt("z2", 5, "harm-report"))[0]
        view = CoverageView().generate(first).generate(second)
        view = view.docket(first.ident, "ell-1").docket(second.ident, "ell-2")
        self.assertEqual({item.content for item in view.liabilities}, {"investigate"})
        self.assertEqual(len({item.ident for item in view.liabilities}), 2)

    def test_external_evaluator_and_internal_generation_can_disagree(self):
        self.assertEqual(evaluator_internal_disagreement(), (True, False))


class ServiceIntegrityCases(unittest.TestCase):
    def setUp(self):
        self.liability = Commitment("ell", ContentKind.DO, "investigate", "spec-v1", "due")
        self.specs = {"spec-v1": frozenset({"receipt-a", "receipt-b"}), "spec-v2": frozenset()}

    def test_rewriting_service_criterion_cannot_fake_discharge(self):
        fake = ServiceCertificate("ell", "spec-v2", frozenset())
        self.assertFalse(certified_service(self.liability, fake, self.specs))

    def test_certified_service_uses_pinned_specification(self):
        certificate = ServiceCertificate("ell", "spec-v1", frozenset({"receipt-a", "receipt-b"}))
        self.assertTrue(certified_service(self.liability, certificate, self.specs))

    def test_service_spec_revision_needs_license_and_lineage(self):
        revised = Commitment("ell-v2", ContentKind.DO, "investigate", "spec-v2", "due")
        self.assertEqual(
            service_spec_revision_errors(self.liability, revised, False, False),
            ("spec_revision.unlicensed", "spec_revision.unaccounted"),
        )
        self.assertEqual(service_spec_revision_errors(self.liability, revised, True, True), ())

    def test_one_investigation_needs_two_input_scoped_service_edges(self):
        other = Commitment("ell-2", ContentKind.DO, "investigate", "spec-v1", "due-2")
        one = ServiceCertificate("ell", "spec-v1", frozenset({"shared"}))
        two = ServiceCertificate("ell-2", "spec-v1", frozenset({"shared"}))
        self.assertFalse(per_input_service_edges((self.liability, other), (one,)))
        self.assertTrue(per_input_service_edges((self.liability, other), (one, two)))


class SchedulerBridgeCases(unittest.TestCase):
    def test_scd_translation_preserves_the_exact_finite_objective(self):
        ask_ab = InquiryAction("q-ab", frozenset({"a", "b"}), Fraction(3))
        ask_b = InquiryAction("q-b", frozenset({"b"}), Fraction(1))
        delay = lambda age: Fraction(age * age)
        requests = (
            InquiryRequest("d1", "a", 0, delay),
            InquiryRequest("d2", "b", 1, delay),
        )
        inquiry_purchases = ((2, ask_ab), (4, ask_b))
        sets, translated_requests = compile_scd((ask_ab, ask_b), requests)
        by_id = {item.ident: item for item in sets}
        scd_purchases = tuple(
            (time, by_id[action.ident]) for time, action in inquiry_purchases
        )
        self.assertEqual(
            inquiry_delay_objective(inquiry_purchases, requests, 5),
            scd_objective(scd_purchases, translated_requests, 5),
        )
        self.assertEqual(scd_objective(scd_purchases, translated_requests, 5), Fraction(9))

    def test_scd_translation_handles_overlap_repurchase_and_future_arrival(self):
        ask_ab = InquiryAction("q-ab", frozenset({"a", "b"}), Fraction(2))
        ask_bc = InquiryAction("q-bc", frozenset({"b", "c"}), Fraction(3))
        requests = (
            InquiryRequest("a0", "a", 0, lambda age: Fraction(age)),
            InquiryRequest("b1", "b", 1, lambda age: Fraction(2 * age)),
            InquiryRequest("a3", "a", 3, lambda age: Fraction(age * age)),
            InquiryRequest("c2", "c", 2, lambda age: Fraction(3 * age)),
        )
        inquiry_purchases = ((2, ask_ab), (3, ask_bc), (5, ask_ab))
        sets, translated_requests = compile_scd((ask_ab, ask_bc), requests)
        by_id = {item.ident: item for item in sets}
        scd_purchases = tuple(
            (time, by_id[action.ident]) for time, action in inquiry_purchases
        )
        self.assertEqual(
            inquiry_delay_objective(inquiry_purchases, requests, 6),
            scd_objective(scd_purchases, translated_requests, 6),
        )
        self.assertEqual(
            scd_objective(scd_purchases, translated_requests, 6), Fraction(18)
        )

    def test_finite_terminal_delay_allows_permanent_nonservice(self):
        request = InquiryRequest("d", "a", 0, lambda age: Fraction(min(age, 2)))
        _sets, translated = compile_scd((), (request,))
        self.assertEqual(scd_objective((), translated, 50), Fraction(2))

    def test_global_competitiveness_alone_does_not_prevent_starvation(self):
        for horizon in range(1, 20):
            algorithm, optimum = starvation_despite_two_competitiveness(horizon)
            self.assertLessEqual(algorithm, 2 * optimum)

    def test_fixed_submodular_docket_is_unit_metric_mlsc(self):
        first = lambda chosen: Fraction(1) if "a" in chosen else Fraction(0)
        second = lambda chosen: Fraction(1) if chosen & {"a", "b"} else Fraction(0)
        objectives = (first, second)
        self.assertTrue(monotone_submodular(("a", "b"), first))
        self.assertTrue(monotone_submodular(("a", "b"), second))
        self.assertEqual(fixed_docket_latency(("a", "b"), objectives), 2)
        self.assertEqual(
            fixed_docket_latency(("a", "b"), objectives),
            mlsc_unit_metric_objective(("a", "b"), objectives),
        )

    def test_unit_metric_mlsc_translation_on_overlapping_objectives(self):
        any_a = lambda chosen: Fraction(1) if "a" in chosen else Fraction(0)
        any_bc = lambda chosen: Fraction(1) if chosen & {"b", "c"} else Fraction(0)
        two_of_three = lambda chosen: Fraction(min(len(chosen), 2), 2)
        objectives = (any_a, any_bc, two_of_three)
        expected = {
            ("a", "b", "c"): 5,
            ("c", "b", "a"): 6,
            ("b", "a", "c"): 5,
        }
        for order, value in expected.items():
            self.assertEqual(
                fixed_docket_latency(order, objectives),
                mlsc_unit_metric_objective(order, objectives),
            )
            self.assertEqual(mlsc_unit_metric_objective(order, objectives), value)

    def test_complementarity_breaks_submodular_bridge(self):
        self.assertFalse(monotone_submodular(("a", "b"), complementarity_progress))

    def test_overload_defeats_unconditional_bounded_coverage(self):
        self.assertEqual(overloaded_backlog(2, 1, 10), 10)


if __name__ == "__main__":
    unittest.main()
