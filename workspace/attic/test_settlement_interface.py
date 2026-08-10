"""WP-0: the interface as a formal object, and its reference witness."""

from __future__ import annotations

import unittest
from dataclasses import replace
from fractions import Fraction as Q

from src.coherence import PriceAssignment, ToleranceDeclaration, ToleranceSchedule
from src.leverage_interval import Book, Endorsement, Language, SettledFact
from src.settlement_interface import (
    ALL_CLAUSES,
    CHECKABLE,
    CHECKABLE_CLAUSES,
    CLAUSE_LEVEL,
    CLAUSE_TEXT,
    DECLARED,
    DECLARED_CLAUSES,
    EMPIRICAL,
    LOGICAL,
    PRECOMMITTED,
    AdmittedQuery,
    BreachRecord,
    DeclaredHypothesis,
    DocketFacts,
    EngineDeclaration,
    EraFacts,
    FundedRequest,
    Pin,
    Position,
    PricedState,
    Procedure,
    ReferenceEngine,
    SettlementRecord,
    SettlementRequestKey,
    adequacy_inequality,
    directional_variants,
    evaluate_interface,
    key_field_names,
    key_from_intent,
    realized_incoherence,
    reference_record,
    report_variable,
    satisfies,
)

ENGINE = ReferenceEngine().declaration
RECORD = reference_record()


def hypotheses_for(*clauses: str) -> tuple[DeclaredHypothesis, ...]:
    return tuple(DeclaredHypothesis(f"H:{c}", c, f"the declared content of {c}",
                                    "the test") for c in clauses)


ALL_DECLARED = hypotheses_for(*(name for name, _ in DECLARED_CLAUSES))


class ClauseInventoryTests(unittest.TestCase):

    def test_every_clause_carries_its_text_and_its_level(self):
        for name, _ in ALL_CLAUSES:
            base = name.split("-persistence")[0].split("-semantics")[0]
            with self.subTest(clause=name):
                self.assertIn(base, CLAUSE_TEXT)
                self.assertIn(base, CLAUSE_LEVEL)
                self.assertTrue(CLAUSE_TEXT[base].strip())

    def test_the_split_between_checkable_and_declared_is_exhaustive(self):
        names = [name for name, _ in ALL_CLAUSES]
        self.assertEqual(len(names), len(set(names)))
        report = evaluate_interface(ENGINE, RECORD, ALL_DECLARED)
        kinds = {v.clause: v.kind for v in report.verdicts}
        for name, _ in CHECKABLE_CLAUSES:
            self.assertEqual(kinds[name], CHECKABLE)
        for name, _ in DECLARED_CLAUSES:
            self.assertEqual(kinds[name], DECLARED)

    def test_every_predicate_docstring_quotes_its_clause(self):
        """The formal object and the prose stay attached to each other."""
        for name, predicate in ALL_CLAUSES:
            with self.subTest(clause=name):
                self.assertTrue(predicate.__doc__)
                self.assertGreater(len(predicate.__doc__), 120)


class ReferenceEngineTests(unittest.TestCase):
    """The existence proof that the checkable fragment is jointly satisfiable."""

    def test_it_satisfies_every_checkable_clause(self):
        report = evaluate_interface(ENGINE, RECORD)
        self.assertTrue(report.checkable_hold, report.obstructions)
        self.assertEqual(
            sorted(report.failing),
            sorted(name for name, _ in DECLARED_CLAUSES))

    def test_the_declared_clauses_fail_loudly_until_supplied(self):
        bare = evaluate_interface(ENGINE, RECORD)
        self.assertFalse(bare.declared_hold)
        self.assertFalse(bare.satisfies_interface)
        supplied = evaluate_interface(ENGINE, RECORD, ALL_DECLARED)
        self.assertTrue(supplied.satisfies_interface)
        self.assertEqual(len(supplied.leaned_on), len(DECLARED_CLAUSES))

    def test_what_was_leaned_on_is_printed_rather_than_absorbed(self):
        report = evaluate_interface(ENGINE, RECORD, ALL_DECLARED)
        for name, _ in DECLARED_CLAUSES:
            self.assertIn(f"H:{name}", report.leaned_on)

    def test_satisfies_is_the_predicate_a_theorem_can_quantify_over(self):
        self.assertTrue(satisfies(ENGINE, RECORD, ALL_DECLARED))
        self.assertFalse(satisfies(ENGINE, RECORD))
        self.assertTrue(satisfies(ENGINE, RECORD, (), clauses=("J1", "J2", "J3")))


class JurisdictionTests(unittest.TestCase):

    def test_a_pin_outside_the_declared_class_is_caught(self):
        stray = Pin(report_variable("proc:undeclared", 1), "proc:undeclared", 1,
                    "warm")
        record = replace(RECORD, pins=RECORD.pins + (stray,))
        verdict = evaluate_interface(ENGINE, record, clauses=("J1",)).by_clause["J1"]
        self.assertFalse(verdict.holds)

    def test_a_value_outside_the_declared_outcome_space_is_caught(self):
        bad = Pin(report_variable("proc:thermometer", 3), "proc:thermometer", 3,
                  "tepid")
        record = replace(RECORD, pins=RECORD.pins + (bad,))
        self.assertFalse(
            evaluate_interface(ENGINE, record, clauses=("J1",)).by_clause["J1"].holds)

    def test_a_second_pin_on_one_variable_is_a_jurisdiction_violation(self):
        """Even when the two values agree: write-once is about the variable."""
        first = RECORD.pins[0]
        record = replace(RECORD, pins=RECORD.pins + (first,))
        verdict = evaluate_interface(ENGINE, record, clauses=("J2",)).by_clause["J2"]
        self.assertFalse(verdict.holds)
        self.assertIn("breach stack", " ".join(verdict.obstructions))

    def test_a_non_owning_engine_cannot_write(self):
        borrowed = replace(ENGINE, procedures=tuple(
            replace(p, owner="engine:other") for p in ENGINE.procedures))
        self.assertFalse(
            evaluate_interface(borrowed, RECORD, clauses=("J2",)).by_clause["J2"].holds)

    def test_translated_content_may_not_be_re_settled(self):
        old = report_variable("proc:thermometer", 1)
        new = report_variable("proc:thermometer", 3)
        record = replace(
            RECORD,
            era=EraFacts(boundaries=(3,), translations=((old, new),)),
            pins=RECORD.pins + (Pin(new, "proc:thermometer", 3, "warm", era=1),))
        verdict = evaluate_interface(ENGINE, record, clauses=("J3",)).by_clause["J3"]
        self.assertFalse(verdict.holds)
        self.assertIn("re-spoken", " ".join(verdict.obstructions))


class ClockTests(unittest.TestCase):

    def test_a_funded_and_run_request_past_its_horizon_must_be_pinned(self):
        record = replace(RECORD, pins=RECORD.pins[1:])
        verdict = evaluate_interface(
            ENGINE, record, clauses=("C1-empirical",)).by_clause["C1-empirical"]
        self.assertFalse(verdict.holds)

    def test_an_unfunded_question_is_not_promised(self):
        """The conditional form is the point: no funding, no obligation."""
        record = replace(RECORD, requests=(), pins=RECORD.pins[1:])
        self.assertTrue(evaluate_interface(
            ENGINE, record, clauses=("C1-empirical",)).by_clause["C1-empirical"].holds)

    def test_an_unripe_query_may_not_accrue_liability(self):
        docket = DocketFacts(capacity=Q(1), queries=(
            AdmittedQuery("q:x", 0, 1, ("proc:thermometer",), Q(1), ripe=False,
                          liability=Q(3)),))
        record = replace(RECORD, docket=docket)
        verdict = evaluate_interface(ENGINE, record, clauses=("C2",)).by_clause["C2"]
        self.assertFalse(verdict.holds)
        self.assertIn("without liability", " ".join(verdict.obstructions))

    def test_a_query_the_horizons_cannot_reach_is_unripe(self):
        docket = DocketFacts(capacity=Q(1), queries=(
            AdmittedQuery("q:x", 0, 1, ("proc:thermometer",), Q(1), ripe=True),))
        record = replace(RECORD, docket=docket)
        self.assertFalse(
            evaluate_interface(ENGINE, record, clauses=("C2",)).by_clause["C2"].holds)

    def test_dependence_on_the_rateless_channel_must_toll(self):
        docket = DocketFacts(capacity=Q(1), queries=(
            AdmittedQuery("q:logical", 0, 9, ("proc:decide",), Q(1), True,
                          tolled=False),))
        record = replace(RECORD, docket=docket)
        verdict = evaluate_interface(ENGINE, record, clauses=("C2",)).by_clause["C2"]
        self.assertFalse(verdict.holds)
        self.assertIn("tolled", " ".join(verdict.obstructions))

    def test_adequacy_is_vacuous_on_a_purely_logical_docket(self):
        """Coherent design, and recorded as coverage of nothing."""
        docket = DocketFacts(capacity=Q(1), queries=(
            AdmittedQuery("q:logical", 0, 9, ("proc:decide",), Q(1), True, True),))
        record = replace(RECORD, docket=docket)
        self.assertEqual(adequacy_inequality(ENGINE, record), ())

    def test_a_deadline_that_ignores_the_upstream_horizon_fails_adequacy(self):
        docket = DocketFacts(capacity=Q(1), queries=(
            AdmittedQuery("q:x", 0, 2, ("proc:thermometer",), Q(2), True),))
        record = replace(RECORD, docket=docket)
        self.assertTrue(adequacy_inequality(ENGINE, record))


class PurseTests(unittest.TestCase):

    def test_the_core_minimum_is_checked_by_program_not_taken_on_trust(self):
        report = evaluate_interface(ENGINE, RECORD, clauses=("P1",))
        self.assertTrue(report.by_clause["P1"].holds)

    def test_an_unsatisfiable_core_minimum_quarantines_force(self):
        """The declared branch fires, and it names itself."""
        demanding = replace(ENGINE, core_minimum=Q(9, 10))
        language = Language(("w1", "w2"), {"A": ("w1",)})
        book = Book(1, (Endorsement("e", (Q(1), Q(0)), Q(1, 2)),))
        state = PricedState(0, language, book, ())
        record = replace(RECORD, priced_states=(state,))
        verdict = evaluate_interface(demanding, record,
                                     clauses=("P1",)).by_clause["P1"]
        self.assertFalse(verdict.holds)
        self.assertIn("quarantine", " ".join(verdict.obstructions).lower())

    def test_persistence_is_declared_and_not_bought_by_the_per_date_check(self):
        checked = evaluate_interface(ENGINE, RECORD, clauses=("P1",))
        self.assertTrue(checked.by_clause["P1"].holds)
        persistence = evaluate_interface(
            ENGINE, RECORD, clauses=("P1-persistence",)).by_clause["P1-persistence"]
        self.assertFalse(persistence.holds,
                         "a per-date program bounds no infimum over time")

    def test_a_downside_limit_needs_a_declared_means(self):
        undeclared = replace(ENGINE, downside_means=None)
        self.assertFalse(
            evaluate_interface(undeclared, RECORD, clauses=("P2",)).by_clause["P2"].holds)

    def test_exposure_beyond_the_declared_limit_is_a_breach(self):
        record = replace(RECORD, worst_case_exposure=Q(-3))
        engine = replace(ENGINE, downside_limit=Q(2))
        self.assertFalse(
            evaluate_interface(engine, record, clauses=("P2",)).by_clause["P2"].holds)

    def test_gating_bounds_what_is_live_per_date(self):
        record = replace(RECORD, live_instruments=((0, 99),))
        self.assertFalse(
            evaluate_interface(ENGINE, record, clauses=("P3",)).by_clause["P3"].holds)

    def test_naming_a_certificate_type_is_not_holding_its_semantics(self):
        named = evaluate_interface(ENGINE, RECORD, clauses=("P4",))
        self.assertTrue(named.by_clause["P4"].holds)
        semantics = evaluate_interface(
            ENGINE, RECORD, clauses=("P4-semantics",)).by_clause["P4-semantics"]
        self.assertFalse(semantics.holds)


class ToleranceClauseTests(unittest.TestCase):

    def test_conformance_reads_the_computed_incoherence(self):
        state = RECORD.priced_states[0]
        self.assertEqual(realized_incoherence(state), Q(0))
        self.assertTrue(
            evaluate_interface(ENGINE, RECORD, clauses=("T1",)).by_clause["T1"].holds)

    def test_prices_above_the_declared_schedule_breach_the_clause(self):
        language = Language(("w1", "w2", "w3"),
                            {"A": ("w1", "w2"), "B": ("w2", "w3"), "C": ("w2",)})
        state = PricedState(0, language, Book(1, ()), (),
                            PriceAssignment(1, {"A": Q(9, 10), "B": Q(9, 10),
                                                "C": Q(0)}))
        record = replace(RECORD, priced_states=(state,))
        verdict = evaluate_interface(ENGINE, record, clauses=("T1",)).by_clause["T1"]
        self.assertFalse(verdict.holds)
        self.assertIn("4/15", " ".join(verdict.obstructions))

    def test_a_misattributed_breach_is_caught(self):
        engine = replace(ENGINE, tolerance=ToleranceSchedule("t", {}, Q(1, 2)))
        breach = BreachRecord(0, ToleranceDeclaration(0, Q(1, 2), Q(1, 4)),
                              Q(3, 4), "book", False, True)
        record = replace(RECORD, breaches=(breach,))
        verdict = evaluate_interface(engine, record, clauses=("T2",)).by_clause["T2"]
        self.assertFalse(verdict.holds)


class ConductTests(unittest.TestCase):

    def test_the_request_key_names_a_question_and_has_no_outcome_field(self):
        self.assertEqual(key_field_names(),
                         ("target", "procedure_id", "funder_id", "requested_date",
                          "scheduled_date"))
        with self.assertRaises(TypeError):
            SettlementRequestKey("t", "p", "f", 0, 1, outcome="warm")

    def test_two_opposite_intents_write_the_same_key(self):
        """Directional funding is unconstructible, not forbidden."""
        first = key_from_intent("X", "p", "funder:a", 0, 1, "warm")
        second = key_from_intent("X", "p", "funder:a", 0, 1, "cold")
        self.assertEqual(first, second)
        self.assertEqual(len(directional_variants(first, ("warm", "cold"))), 1)

    def test_a_precommitted_rule_must_be_honoured(self):
        late = replace(RECORD.requests[0], executed_date=3)
        record = replace(RECORD, requests=(late,))
        self.assertFalse(
            evaluate_interface(ENGINE, record, clauses=("F2",)).by_clause["F2"].holds)

    def test_a_fresh_funder_position_inside_the_window_fires(self):
        position = Position("funder:a", RECORD.requests[0].key.target, 1)
        record = replace(RECORD, positions=(position,))
        verdict = evaluate_interface(ENGINE, record, clauses=("F3",)).by_clause["F3"]
        self.assertFalse(verdict.holds)

    def test_a_position_outside_the_window_is_not_the_objection(self):
        position = Position("funder:a", RECORD.requests[0].key.target, 4)
        record = replace(RECORD, positions=(position,))
        self.assertTrue(
            evaluate_interface(ENGINE, record, clauses=("F3",)).by_clause["F3"].holds)

    def test_a_funded_pin_must_record_its_funder(self):
        anonymous = replace(RECORD.pins[0], funder_profile=())
        record = replace(RECORD, pins=(anonymous,) + RECORD.pins[1:])
        self.assertFalse(
            evaluate_interface(ENGINE, record, clauses=("F4",)).by_clause["F4"].holds)

    def test_a_logical_pin_must_ship_a_derivation(self):
        bare = replace(RECORD.pins[1], derivation=None)
        record = replace(RECORD, pins=RECORD.pins[:1] + (bare,))
        verdict = evaluate_interface(
            ENGINE, record, clauses=("S8-logical",)).by_clause["S8-logical"]
        self.assertFalse(verdict.holds)


if __name__ == "__main__":
    unittest.main()
