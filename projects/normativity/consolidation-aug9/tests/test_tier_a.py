"""Tier A: the load-bearing computations, against folder-local implementations.

Every displayed instance in the monograph that carries an exact number is
recomputed here. Passing is evidence for these displayed finite instances only.
"""

from __future__ import annotations

import unittest
from dataclasses import replace
from fractions import Fraction as Q

from src.coherence import (
    BOOK_BREACH,
    ENGINE_BREACH,
    EXACT,
    NO_BREACH,
    Layering,
    Prices,
    Schedule,
    attribute,
    certified_excess,
    incoherence,
    prices_are_coherent,
    reduces_at_zero,
    relax,
    robust_interval,
    robust_merits,
    robust_sure_loss,
    tolerance_is_working,
    verify,
    working_boundary,
)
from src.composite import (
    DECLARED_CLAUSES,
    Docket,
    Parameters,
    Position,
    PricedState,
    Query,
    Settlement,
    directional_variants,
    evaluate,
    full_hypotheses,
    key_fields,
    key_from_intent,
    movement_recursion,
    parametric_composite,
    reference_engine,
    reference_record,
    report_variable,
    wealth_cap,
)
from src.constructions import (
    CROSSING_TRANSFER,
    EMPIRICAL_FENCE,
    FENCED_TRANSFER,
    LOGICAL,
    POOLED,
    THERMOMETER_A,
    WORLD,
    BridgeWarrant,
    Inference,
    Instrument,
    LookupProver,
    blackout_grounds,
    common_source_grounds,
    compose_purse,
    constrain,
    constructed_channel,
    crosses,
    disagreement_witness,
    execute,
    executor_is_blind,
    grounding,
    jurisdictions_disjoint,
    precommitted,
    quarantine,
    recorded,
    resolve,
    ripeness_gate,
    run_request,
    serve,
    settlement_has_no_answerability_columns,
    settlement_request,
    stopping_is_outcome_independent,
    adequacy_implies_deadlines,
    two_engine_instance,
)
from src.core import (
    QUARANTINE,
    accumulate,
    admissible_reference,
    ambient_core_holds,
    ambient_voids_nondegenerate,
    ambient_voids_two_sentence,
    clipping_adapter,
    coefficient_upper_bound,
    confirmed_by,
    dependent_settlement,
    endorsement_rows,
    max_coefficient,
    relative_core_holds,
    relative_vertices,
    single_row_coefficient,
    sweep,
    transport,
)
from src.exact import Constraint, solve_square
from src.grammar import (
    CATALOG,
    CATALOG_BY_ID,
    REGISTRY,
    Grounds,
    ablate,
    evidence_classes,
    footprint_classes,
    judge,
    legacy_classes,
    splits_against_legacy,
)
from src.interval import (
    Book,
    Endorsement,
    Language,
    SettledFact,
    coherence_polytope,
    compute_interval,
    docket_polytope,
    threshold_direction,
)
from src.composite import adequacy

LANGUAGE = Language(("w1", "w2", "w3"),
                    {"A": ("w1", "w2"), "B": ("w2", "w3"), "C": ("w2",)})
BOOK = Book(1, (Endorsement("e:A", (Q(1), Q(1), Q(0)), Q(3, 5)),
                Endorsement("e:B", (Q(0), Q(1), Q(1)), Q(4, 5))))
COHERENT = Prices(1, {"A": Q(9, 10), "B": Q(1, 10)})
INCOHERENT = Prices(1, {"A": Q(9, 10), "B": Q(9, 10), "C": Q(0)})


class ExactArithmeticTests(unittest.TestCase):

    def test_singular_systems_are_reported_not_approximated(self):
        self.assertIsNone(solve_square([[Q(1), Q(1)], [Q(2), Q(2)]], [Q(1), Q(2)]))

    def test_solutions_are_exact_rationals(self):
        solution = solve_square([[Q(1), Q(1)], [Q(1), Q(-1)]], [Q(1), Q(1, 3)])
        self.assertEqual(solution, (Q(2, 3), Q(1, 3)))


class IntervalTests(unittest.TestCase):

    def test_the_two_polytopes_are_distinct(self):
        engine_side = coherence_polytope(LANGUAGE, ())
        docket_side = docket_polytope(LANGUAGE, BOOK, ())
        self.assertNotEqual(engine_side, docket_side)
        self.assertFalse(any(r.source.startswith("book:") for r in engine_side))
        self.assertTrue(any(r.source.startswith("book:") for r in docket_side))

    def test_the_interval_is_exact_with_a_witness(self):
        interval = compute_interval(LANGUAGE, BOOK, (), "A")
        self.assertEqual((interval.lower, interval.upper), (Q(3, 5), Q(1)))
        self.assertEqual(sum(interval.lower_witness.assignment), Q(1))

    def test_an_unlicensed_target_is_refused_not_priced_at_zero(self):
        interval = compute_interval(LANGUAGE, BOOK, (), "Z")
        self.assertFalse(interval.licensed)
        self.assertIsNone(threshold_direction(interval, Q(1, 2)))

    def test_an_infeasible_book_is_reported(self):
        book = Book(2, (Endorsement("hi", (Q(1), Q(1), Q(0)), Q(3, 4)),
                        Endorsement("lo", (Q(-1), Q(-1), Q(0)), Q(-1, 4))))
        self.assertTrue(compute_interval(LANGUAGE, book, (), "A").infeasible)


class IncoherenceTests(unittest.TestCase):

    def test_the_value_is_the_hand_computed_rational(self):
        """A + B - C = 1 forces the three prices apart by exactly 4/15."""
        report = incoherence(LANGUAGE, (), INCOHERENT)
        self.assertEqual(report.value, Q(4, 15))
        self.assertEqual(sum(report.witness), Q(1))

    def test_the_certificate_is_normalized_and_tight(self):
        report = incoherence(LANGUAGE, (), INCOHERENT)
        self.assertEqual(report.certificate.mass, Q(1))
        self.assertEqual(report.certificate.excess, Q(4, 15))
        self.assertTrue(verify(LANGUAGE, (), INCOHERENT, report.certificate))

    def test_the_certificate_is_recomputed_independently(self):
        report = incoherence(LANGUAGE, (), INCOHERENT)
        self.assertEqual(
            certified_excess(LANGUAGE, (), INCOHERENT, report.certificate.multipliers),
            report.value)

    def test_zero_exactly_when_coherent(self):
        self.assertEqual(incoherence(LANGUAGE, (), COHERENT).value, Q(0))
        self.assertTrue(prices_are_coherent(LANGUAGE, (), COHERENT))
        self.assertFalse(prices_are_coherent(LANGUAGE, (), INCOHERENT))

    def test_monotone_under_adding_a_settlement(self):
        before = incoherence(LANGUAGE, (), INCOHERENT).value
        after = incoherence(LANGUAGE, (SettledFact("C", Q(1, 2)),), INCOHERENT).value
        self.assertGreaterEqual(after, before)

    def test_a_coherent_engine_is_never_charged_for_an_infeasible_book(self):
        """The guard on the two polytopes: the wrong party would otherwise pay."""
        book = Book(2, (Endorsement("hi", (Q(1), Q(1), Q(0)), Q(3, 4)),
                        Endorsement("lo", (Q(-1), Q(-1), Q(0)), Q(-1, 4))))
        prices = Prices(2, {"A": Q(1, 2)})
        self.assertTrue(compute_interval(LANGUAGE, book, (), "A").infeasible)
        self.assertEqual(incoherence(LANGUAGE, (), prices).value, Q(0))
        self.assertEqual(attribute(Layering(0, Q(0)), Q(0)).party, NO_BREACH)


class RobustDocketTests(unittest.TestCase):

    def test_relaxation_never_touches_a_settlement_or_the_simplex(self):
        settled = (SettledFact("C", Q(1, 5)),)
        base = docket_polytope(LANGUAGE, BOOK, settled)
        for before, after in zip(base, relax(base, Q(1, 3))):
            if before.source.startswith(("simplex.", "settled:")):
                self.assertEqual(before, after)
            else:
                self.assertLess(after.rhs, before.rhs)

    def test_the_robust_forms_reduce_at_zero(self):
        self.assertTrue(reduces_at_zero(LANGUAGE, BOOK, (), "A"))
        self.assertEqual(robust_interval(LANGUAGE, BOOK, (), "A", Q(0)),
                         compute_interval(LANGUAGE, BOOK, (), "A"))

    def test_the_interval_widens_monotonically(self):
        widths = [robust_interval(LANGUAGE, BOOK, (), "A", t).upper
                  - robust_interval(LANGUAGE, BOOK, (), "A", t).lower
                  for t in (Q(0), Q(1, 20), Q(1, 5), Q(1, 2))]
        self.assertEqual(widths, sorted(widths))

    def test_the_boundary_is_exactly_one_tenth(self):
        working, failing = working_boundary(LANGUAGE, BOOK, (), "A", Q(1, 2))
        self.assertLessEqual(working, Q(1, 10))
        self.assertGreater(failing, Q(1, 10))
        self.assertTrue(tolerance_is_working(LANGUAGE, BOOK, (), "A", Q(1, 2), Q(1, 10)))
        self.assertFalse(tolerance_is_working(LANGUAGE, BOOK, (), "A", Q(1, 2),
                                              Q(1, 10) + Q(1, 240)))
        self.assertEqual(robust_interval(LANGUAGE, BOOK, (), "A", Q(1, 10)).lower,
                         Q(1, 2))

    def test_a_maximal_declaration_is_sound_and_useless(self):
        interval = robust_interval(LANGUAGE, BOOK, (), "A", Q(1))
        self.assertEqual((interval.lower, interval.upper), (Q(0), Q(1)))
        self.assertFalse(tolerance_is_working(LANGUAGE, BOOK, (), "A", Q(1, 2), Q(1)))

    def test_the_boundary_is_not_the_degeneration(self):
        interval = robust_interval(LANGUAGE, BOOK, (), "A", Q(1, 10))
        self.assertNotEqual((interval.lower, interval.upper), (Q(0), Q(1)))

    def test_the_sure_loss_objection_fires_only_above_the_schedule(self):
        self.assertIsNone(robust_sure_loss(LANGUAGE, (), INCOHERENT, Q(1, 3)))
        grounds = robust_sure_loss(LANGUAGE, (), INCOHERENT, Q(1, 5))
        self.assertIsNotNone(grounds)
        self.assertEqual(grounds["excess"], Q(4, 15))
        self.assertLessEqual(grounds["mass"], Q(1))

    def test_merits_certification_at_zero_is_the_exact_form(self):
        certificate = robust_merits(LANGUAGE, BOOK, (), "A", Q(1, 2), Q(0), "c:0")
        self.assertEqual(certificate.direction, "positive")
        self.assertEqual(certificate.interval, compute_interval(LANGUAGE, BOOK, (), "A"))


class LayeringTests(unittest.TestCase):

    def test_the_engine_carries_a_breach_of_its_own_certification(self):
        a = attribute(Layering(3, Q(1, 2), Q(1, 4)), Q(3, 4))
        self.assertEqual(a.party, ENGINE_BREACH)
        self.assertTrue(a.tolled)
        self.assertFalse(a.chargeable)

    def test_the_book_carries_a_breach_of_its_own_tighter_bound(self):
        a = attribute(Layering(3, Q(1, 2), Q(1, 4)), Q(1, 3))
        self.assertEqual(a.party, BOOK_BREACH)
        self.assertTrue(a.chargeable)
        self.assertFalse(a.tolled)

    def test_within_every_tolerance_nothing_fires(self):
        self.assertEqual(attribute(Layering(3, Q(1, 2), Q(1, 4)), Q(1, 5)).party,
                         NO_BREACH)

    def test_a_book_tolerance_looser_than_the_engine_is_refused(self):
        with self.assertRaises(ValueError):
            attribute(Layering(0, Q(1, 4), Q(1, 2)), Q(0))

    def test_the_layering_route_supplies_a_working_tolerance(self):
        self.assertFalse(tolerance_is_working(LANGUAGE, BOOK, (), "A", Q(1, 2), Q(1)))
        self.assertTrue(tolerance_is_working(LANGUAGE, BOOK, (), "A", Q(1, 2), Q(1, 20)))
        self.assertEqual(attribute(Layering(0, Q(1), Q(1, 20)), Q(1, 10)).party,
                         BOOK_BREACH)


class CoreGeometryTests(unittest.TestCase):

    def test_the_ambient_reading_voids_at_every_coefficient(self):
        w = ambient_voids_two_sentence()
        self.assertTrue(all(not holds for _, holds in w["ambient"]))
        self.assertTrue(all(holds for _, holds in w["relative"]))

    def test_the_voiding_is_not_a_collapsed_region_artifact(self):
        w = ambient_voids_nondegenerate()
        self.assertGreater(len(relative_vertices(w["language"], w["settled"])), 1)
        self.assertTrue(all(not holds for _, holds in w["ambient"]))
        self.assertTrue(all(holds for _, holds in w["relative"]))

    def test_an_unsettled_region_does_not_void(self):
        language = Language(("w1", "w2"), {"A": ("w1",), "B": ("w2",)})
        self.assertTrue(ambient_core_holds(language, Book(1, ()), (),
                                           (Q(1, 2), Q(1, 2)), Q(1)))

    def test_the_closed_form_is_the_search(self):
        language = Language(("w1", "w2", "w3"),
                            {"A": ("w1",), "B": ("w2",), "C": ("w3",)})
        book = Book(1, (Endorsement("e:A", (Q(1), Q(0), Q(0)), Q(1, 2)),))
        bound = max_coefficient(language, book, ())
        self.assertTrue(bound.exact)
        self.assertEqual(bound.working, Q(1, 2))
        self.assertEqual(bound.witness, (Q(1), Q(0), Q(0)))
        self.assertEqual(single_row_coefficient(Q(0), Q(1, 2), Q(1)), Q(1, 2))

    def test_the_per_row_bound_caps_the_joint_problem(self):
        language = Language(("w1", "w2", "w3"),
                            {"A": ("w1",), "B": ("w2",), "C": ("w3",)})
        book = Book(1, (Endorsement("e:A", (Q(1), Q(0), Q(0)), Q(1, 2)),
                        Endorsement("e:B", (Q(0), Q(1), Q(0)), Q(1, 4))))
        self.assertLessEqual(
            max_coefficient(language, book, ()).working,
            coefficient_upper_bound(relative_vertices(language, ()),
                                    endorsement_rows(language, book)))

    def test_emptiness_is_a_declared_branch(self):
        language = Language(("w1", "w2"), {"A": ("w1",)})
        book = Book(1, (Endorsement("e", (Q(1), Q(0)), Q(1, 2)),))
        admission = clipping_adapter(language, book, (), Q(9, 10), 0)
        self.assertFalse(admission.admitted)
        self.assertEqual(admission.consequence, QUARANTINE)
        self.assertEqual(admission.core_minimum, Q(9, 10))

    def test_an_admissible_reference_really_admits(self):
        language = Language(("w1", "w2", "w3"),
                            {"A": ("w1",), "B": ("w2",), "C": ("w3",)})
        book = Book(1, (Endorsement("e:A", (Q(1), Q(0), Q(0)), Q(1, 2)),))
        reference = admissible_reference(language, book, (), Q(1, 4))
        self.assertTrue(relative_core_holds(language, book, (), reference, Q(1, 4)))


class TransportTests(unittest.TestCase):

    def setUp(self):
        w = dependent_settlement()
        self.language, self.book = w["language"], w["book"]
        self.reference = w["reference"]
        self.dependent, self.confirmed = w["dependent"], w["confirmed"]

    def test_independence_is_the_reference_confirming_the_settlement(self):
        self.assertTrue(confirmed_by(self.language, self.reference, self.confirmed))
        self.assertFalse(confirmed_by(self.language, self.reference, self.dependent))

    def test_transport_holds_across_a_confirmed_settlement(self):
        self.assertTrue(transport(self.language, self.book, (), self.reference,
                                  Q(1, 2), self.confirmed))

    def test_transport_is_stated_only_for_confirmed_settlements(self):
        with self.assertRaises(ValueError):
            transport(self.language, self.book, (), self.reference, Q(1, 2),
                      self.dependent)

    def test_the_dependent_settlement_destroys_what_the_confirmed_one_keeps(self):
        before = max_coefficient(self.language, self.book, ())
        after_d = max_coefficient(self.language, self.book, (self.dependent,))
        after_c = max_coefficient(self.language, self.book, (self.confirmed,))
        self.assertEqual((before.working, after_c.working, after_d.working),
                         (Q(1, 2), Q(1, 2), Q(0)))
        self.assertTrue(after_d.exact)

    def test_every_confirmed_settlement_in_the_sweep_transports(self):
        report = sweep()
        self.assertEqual(report["confirmed_transport"], report["confirmed_total"])
        self.assertEqual(report["confirmed_total"], 8)

    def test_dependent_settlements_are_where_the_coefficient_is_lost(self):
        report = sweep()
        self.assertEqual(report["dependent_total"], 28)
        self.assertEqual(len(report["collapsed"]), 6)
        self.assertEqual(len(report["reduced"]), 6)
        for _, _, _, before, after in report["reduced"]:
            self.assertLess(after, before)

    def test_a_trajectory_reports_only_its_searched_minimum(self):
        language = Language(("w1", "w2", "w3"),
                            {"A": ("w1",), "B": ("w2",), "C": ("w3",)})
        book = Book(1, (Endorsement("e:A", (Q(1), Q(0), Q(0)), Q(1, 4)),))
        report = accumulate(language, book,
                            (SettledFact("B", Q(0)), SettledFact("C", Q(0))), Q(1, 8))
        self.assertTrue(report.survives)
        self.assertEqual(report.minimum, min(report.coefficients))

    def test_a_declared_minimum_can_fail_on_a_trajectory(self):
        language = Language(("w1", "w2", "w3"),
                            {"A": ("w1",), "B": ("w2",), "C": ("w3",)})
        book = Book(1, (Endorsement("e:A", (Q(1), Q(0), Q(0)), Q(1, 2)),))
        report = accumulate(language, book, (SettledFact("B", Q(1, 2)),), Q(1, 8))
        self.assertFalse(report.survives)
        self.assertEqual(report.minimum, Q(0))


class InterfaceTests(unittest.TestCase):

    def setUp(self):
        self.d, self.r = reference_engine(), reference_record()

    def test_the_reference_engine_satisfies_every_checkable_clause(self):
        report = evaluate(self.d, self.r)
        self.assertTrue(report.checkable_hold, report.obstructions)
        self.assertEqual(sorted(report.failing),
                         sorted(n for n, _ in DECLARED_CLAUSES))

    def test_the_declared_clauses_fail_until_supplied(self):
        self.assertFalse(evaluate(self.d, self.r).satisfies)
        supplied = evaluate(self.d, self.r, full_hypotheses("test"))
        self.assertTrue(supplied.satisfies)
        self.assertEqual(len(supplied.leaned_on), len(DECLARED_CLAUSES))

    def test_a_second_settlement_on_one_variable_is_a_violation(self):
        record = replace(self.r, settlements=self.r.settlements + (self.r.settlements[0],))
        self.assertFalse(evaluate(self.d, record, clauses=("J2",)).by_clause["J2"].holds)

    def test_a_value_outside_the_outcome_space_is_caught(self):
        bad = Settlement(report_variable("proc:thermometer", 3), "proc:thermometer", 3,
                         "tepid")
        record = replace(self.r, settlements=self.r.settlements + (bad,))
        self.assertFalse(evaluate(self.d, record, clauses=("J1",)).by_clause["J1"].holds)

    def test_an_unripe_query_may_not_accrue_liability(self):
        docket = Docket(Q(1), (Query("q:x", 0, 1, ("proc:thermometer",), Q(1),
                                     ripe=False, liability=Q(3)),))
        record = replace(self.r, docket=docket)
        self.assertFalse(evaluate(self.d, record, clauses=("C2",)).by_clause["C2"].holds)

    def test_dependence_on_the_rateless_channel_must_toll(self):
        docket = Docket(Q(1), (Query("q:l", 0, 9, ("proc:decide",), Q(1), True, False),))
        record = replace(self.r, docket=docket)
        self.assertFalse(evaluate(self.d, record, clauses=("C2",)).by_clause["C2"].holds)

    def test_adequacy_is_vacuous_on_a_purely_logical_docket(self):
        docket = Docket(Q(1), (Query("q:l", 0, 9, ("proc:decide",), Q(1), True, True),))
        self.assertEqual(adequacy(self.d, replace(self.r, docket=docket)), ())

    def test_an_unsatisfiable_core_minimum_quarantines_force(self):
        demanding = replace(self.d, core_minimum=Q(9, 10))
        language = Language(("w1", "w2"), {"A": ("w1",)})
        book = Book(1, (Endorsement("e", (Q(1), Q(0)), Q(1, 2)),))
        record = replace(self.r, priced_states=(PricedState(0, language, book, ()),))
        verdict = evaluate(demanding, record, clauses=("P1",)).by_clause["P1"]
        self.assertFalse(verdict.holds)
        self.assertIn("quarantine", " ".join(verdict.obstructions).lower())

    def test_persistence_is_not_bought_by_the_per_date_check(self):
        self.assertTrue(evaluate(self.d, self.r, clauses=("P1",)).by_clause["P1"].holds)
        self.assertFalse(evaluate(self.d, self.r, clauses=("P1-persistence",)
                                  ).by_clause["P1-persistence"].holds)

    def test_prices_above_the_schedule_breach_the_tolerance_clause(self):
        state = PricedState(0, LANGUAGE, Book(1, ()), (), INCOHERENT)
        record = replace(self.r, priced_states=(state,))
        verdict = evaluate(self.d, record, clauses=("T1",)).by_clause["T1"]
        self.assertFalse(verdict.holds)
        self.assertIn("4/15", " ".join(verdict.obstructions))

    def test_the_key_has_no_outcome_field(self):
        self.assertEqual(key_fields(), ("target", "procedure_id", "funder_id",
                                        "requested_date", "scheduled_date"))
        self.assertEqual(key_from_intent("X", "p", "f", 0, 1, "warm"),
                         key_from_intent("X", "p", "f", 0, 1, "cold"))
        self.assertEqual(len(directional_variants(
            key_from_intent("X", "p", "f", 0, 1, "warm"), ("warm", "cold"))), 1)

    def test_a_fresh_funder_position_inside_the_window_fires(self):
        position = Position("funder:a", self.r.requests[0].key.target, 1)
        record = replace(self.r, positions=(position,))
        self.assertFalse(evaluate(self.d, record, clauses=("F3",)).by_clause["F3"].holds)

    def test_a_logical_settlement_must_ship_a_derivation(self):
        bare = replace(self.r.settlements[1], derivation=None)
        record = replace(self.r, settlements=self.r.settlements[:1] + (bare,))
        self.assertFalse(evaluate(self.d, record, clauses=("S8-logical",)
                                  ).by_clause["S8-logical"].holds)


class ParametricCompositeTests(unittest.TestCase):

    def setUp(self):
        self.d, self.r = reference_engine(), reference_record()
        self.p = Parameters(Q(0), Q(2), Q(0), 1)
        self.h = full_hypotheses("test")

    def test_it_yields_the_bound_when_every_hypothesis_is_in_place(self):
        v = parametric_composite(self.d, self.r, self.p, self.h)
        self.assertTrue(v.holds, v.obstructions)
        caps = movement_recursion(Q(1, 4), Q(0), Q(2), Q(0), 1)
        self.assertEqual(v.movement_cap, caps[1])
        self.assertEqual(v.bound, wealth_cap(Q(1, 4), Q(0), Q(2), caps[1]))
        self.assertEqual(v.bound, Q(30))

    def test_it_reports_no_bound_when_a_hypothesis_is_missing(self):
        v = parametric_composite(self.d, self.r, self.p)
        self.assertFalse(v.holds)
        self.assertIsNone(v.bound)

    def test_every_hypothesis_is_individually_load_bearing(self):
        self.assertEqual(len(self.h), 13)
        for omitted in self.h:
            kept = tuple(x for x in self.h if x is not omitted)
            with self.subTest(omitted=omitted.clause):
                v = parametric_composite(self.d, self.r, self.p, kept)
                self.assertFalse(v.holds)
                self.assertIsNone(v.bound)
                self.assertIn(omitted.clause, v.missing + v.failing_clauses)

    def test_a_failing_checkable_clause_blocks_the_theorem(self):
        record = replace(self.r, worst_case_exposure=Q(-9))
        v = parametric_composite(replace(self.d, downside_limit=Q(2)), record, self.p,
                                 self.h)
        self.assertFalse(v.holds)
        self.assertIn("P2", v.failing_clauses)

    def test_the_bound_degrades_as_the_core_minimum_shrinks(self):
        bounds = []
        for theta in (Q(2, 5), Q(1, 4), Q(1, 10), Q(1, 100)):
            v = parametric_composite(replace(self.d, core_minimum=theta), self.r,
                                     self.p, self.h)
            self.assertTrue(v.holds, v.obstructions)
            bounds.append(v.bound)
        self.assertEqual(bounds, sorted(bounds))

    def test_a_core_minimum_the_record_cannot_support_is_refused(self):
        v = parametric_composite(replace(self.d, core_minimum=Q(1, 2)), self.r, self.p,
                                 self.h)
        self.assertFalse(v.holds)
        self.assertIn("P1", v.failing_clauses)


class ChannelTests(unittest.TestCase):

    def setUp(self):
        self.c = constructed_channel()

    def test_the_settlement_reports_what_the_world_returned(self):
        self.assertEqual(self.c["execution"].settlement.value, "warm")
        self.assertFalse(self.c["execution"].missed_horizon)

    def test_the_executor_cannot_see_the_book_or_the_purse(self):
        self.assertTrue(executor_is_blind())
        self.assertTrue(settlement_has_no_answerability_columns())

    def test_a_value_outside_the_declared_space_is_refused(self):
        with self.assertRaises(ValueError):
            execute(THERMOMETER_A, 1, {("proc:thermometer-a", 1): "tepid"})

    def test_a_silent_world_past_the_horizon_is_a_missed_horizon(self):
        request = settlement_request(report_variable("proc:thermometer-a", 1),
                                     THERMOMETER_A, "funder:a", 0, 1, Q(1), "r:s")
        outcome = run_request(request, THERMOMETER_A, {}, 9)
        self.assertIsNone(outcome.settlement)
        self.assertTrue(outcome.missed_horizon)

    def test_a_settlement_constrains_the_region_permanently(self):
        variable = report_variable("proc:thermometer-a", 1)
        language = Language(("hot", "mild"), {variable: ("hot",), "H": ("hot",)})
        before = constrain(language, Book(1, ()), (), {}, "H")
        after = constrain(language, Book(1, ()), (self.c["execution"].settlement,),
                          {"warm": Q(1), "cold": Q(0)}, "H")
        self.assertEqual((before.lower, before.upper), (Q(0), Q(1)))
        self.assertEqual((after.lower, after.upper), (Q(1), Q(1)))

    def test_a_settlement_pays_the_instruments_referencing_it(self):
        event = self.c["execution"].settlement
        instrument = Instrument("i:1", event.variable_id, "holder", "counterparty",
                                {"warm": Q(3), "cold": Q(0)})
        transfers = resolve((instrument,), event)
        self.assertEqual((len(transfers), transfers[0].amount), (1, Q(3)))

    def test_a_settlement_grounds_evidence_only_through_an_endorsed_bridge(self):
        event = self.c["execution"].settlement
        good = BridgeWarrant("w", event.variable_id, "hot", "supports")
        bad = BridgeWarrant("w", event.variable_id, "hot", "supports", endorsed=False)
        self.assertIsNotNone(grounding(event, "hot", good, "g:1"))
        self.assertIsNone(grounding(event, "hot", bad, "g:2"))

    def test_an_unripe_query_is_refused_without_liability(self):
        verdict = ripeness_gate(Query("q:r", 0, 1, ("proc:thermometer-a",), Q(1)),
                                self.c["procedures"])
        self.assertFalse(verdict.ripe)
        self.assertEqual(verdict.liability, Q(0))

    def test_a_missed_horizon_charges_the_book_nothing(self):
        from src.constructions import toll_missed_horizon

        toll = toll_missed_horizon(Query("q:l", 0, 9, ("proc:thermometer-a",), Q(1)),
                                   THERMOMETER_A, 5)
        self.assertEqual(toll.tolled_dates, 3)
        self.assertFalse(toll.chargeable_to_book)

    def test_adequacy_implies_every_deadline_is_met(self):
        self.assertEqual(adequacy_implies_deadlines(self.c["engine"], self.c["record"]),
                         (True, True))

    def test_a_deadline_too_tight_fails_and_is_missed(self):
        tight = constructed_channel(deadline=4)
        self.assertEqual(adequacy_implies_deadlines(tight["engine"], tight["record"]),
                         (False, False))
        obstructions = " ".join(adequacy(tight["engine"], tight["record"]))
        self.assertIn("per-query adequacy inequality", obstructions)
        self.assertIn("window", obstructions)

    def test_capacity_alone_can_break_adequacy(self):
        docket = Docket(Q(1), (
            Query("q:1", 0, 4, ("proc:thermometer-a",), Q(2), True),
            Query("q:2", 0, 4, ("proc:thermometer-a",), Q(2), True)))
        record = replace(self.c["record"], docket=docket)
        self.assertTrue(any("window" in o for o in adequacy(self.c["engine"], record)))
        self.assertFalse(all(s.met for s in serve(self.c["engine"], docket, 6)))


class ConductTests(unittest.TestCase):

    def setUp(self):
        self.c = constructed_channel()
        self.request = recorded(self.c["execution"])

    def test_a_precommitted_rule_is_checkable(self):
        self.assertTrue(precommitted(self.request))
        self.assertFalse(precommitted(replace(self.request, executed_date=4)))

    def test_the_stop_date_does_not_depend_on_the_outcome(self):
        worlds = ({("proc:thermometer-a", 1): "warm"},
                  {("proc:thermometer-a", 1): "cold"})
        self.assertTrue(stopping_is_outcome_independent(self.c["request"],
                                                        THERMOMETER_A, worlds, 6))

    def test_the_blackout_objection_fires_and_its_controls_do_not(self):
        target = self.request.key.target
        self.assertIsNotNone(blackout_grounds(
            self.request, (Position("funder:a", target, 1),), "g:fire"))
        for control in (Position("funder:a", target, 5),
                        Position("funder:b", target, 1),
                        Position("funder:a", target, 1, fresh=False)):
            with self.subTest(control=control):
                self.assertIsNone(blackout_grounds(self.request, (control,), "g:none"))

    def test_the_blackout_judge_accepts_under_its_footprint(self):
        target = self.request.key.target
        position = Position("funder:a", target, 1)
        grounds = blackout_grounds(self.request, (position,), "g:fire")
        tables = {"settlement.requests": {self.request.request_id: {
                      "funder_id": "funder:a", "target": target}},
                  "positions": {"p:1": {"actor_id": "funder:a", "target": target,
                                        "date": 1, "fresh": True}}}
        verdict = judge(CATALOG_BY_ID["probe-blackout"], tables, grounds)
        self.assertTrue(verdict.accepted, verdict.obstructions)
        self.assertTrue(verdict.upheld)

    def test_the_common_source_objection_fires_on_one_purse_only(self):
        shared = (Settlement("X[a@1]", "pa", 1, "warm", ("funder:a",)),
                  Settlement("X[b@1]", "pb", 1, "cold", ("funder:a",)))
        split = (shared[0], Settlement("X[b@1]", "pb", 1, "cold", ("funder:b",)))
        inference = Inference("hot", ("X[a@1]", "X[b@1]"))
        self.assertIsNotNone(common_source_grounds(inference, shared, "g:c"))
        self.assertIsNone(common_source_grounds(inference, split, "g:n"))

    def test_the_common_source_judge_accepts_under_its_footprint(self):
        events = (Settlement("X[a@1]", "pa", 1, "warm", ("funder:a",)),
                  Settlement("X[b@1]", "pb", 1, "cold", ("funder:a",)))
        grounds = common_source_grounds(Inference("hot", ("X[a@1]", "X[b@1]")), events,
                                        "g:c")
        tables = {"settlement.record": {e.variable_id: {
            "funder_profile": e.funder_profile} for e in events}}
        verdict = judge(CATALOG_BY_ID["common-source"], tables, grounds)
        self.assertTrue(verdict.accepted, verdict.obstructions)
        self.assertTrue(verdict.upheld)


class TwoEngineTests(unittest.TestCase):

    def setUp(self):
        self.i = two_engine_instance()

    def test_the_jurisdictions_are_disjoint(self):
        self.assertEqual(self.i["disjoint"], ())

    def test_an_overlap_is_caught(self):
        clash = replace(self.i["empirical"], procedures=self.i["logical"].procedures)
        self.assertTrue(jurisdictions_disjoint((self.i["logical"], clash)))

    def test_the_deductive_engine_satisfies_the_checkable_clauses(self):
        report = evaluate(self.i["logical"], self.i["record"])
        self.assertTrue(report.checkable_hold, report.obstructions)

    def test_every_logical_settlement_ships_a_derivation(self):
        self.assertTrue(all(s.derivation for s in LookupProver().settlements(1)))

    def test_redundancy_never_reaches_the_settled_record(self):
        w = disagreement_witness()
        self.assertTrue(w.distinct_variables)
        self.assertFalse(w.settlement_conflict)
        self.assertNotEqual(w.events[0].value, w.events[1].value)
        self.assertEqual({x.world_claim for x in w.warrants}, {"the room is hot"})
        self.assertEqual({x.direction for x in w.warrants}, {"supports", "undercuts"})

    def test_the_disagreement_surfaces_in_the_answerable_layer(self):
        self.assertTrue(disagreement_witness().region_infeasible)

    def test_breach_isolation_separates_the_two_tolling_causes(self):
        clocks = quarantine("empirical", (("q:w", "empirical"), ("q:p", LOGICAL)))
        empirical = [c for c in clocks if c.channel == "empirical"]
        logical = [c for c in clocks if c.channel == LOGICAL]
        self.assertTrue(all(c.frozen for c in empirical))
        self.assertTrue(all(not c.frozen and not c.tolled_by_breach for c in logical))
        self.assertTrue(all(c.tolled_rateless and c.tolled for c in logical))

    def test_the_purse_composes_inside_its_fences(self):
        engines = (self.i["logical"], self.i["empirical"])
        exposures = {"engine:deductive": Q(0), "engine:empirical": Q(2)}
        purse = compose_purse(engines, exposures)
        self.assertEqual(purse.fenced_sum, Q(2))
        self.assertTrue(purse.within_limits)
        self.assertIsNotNone(compose_purse(engines, exposures,
                                           (CROSSING_TRANSFER,)).crossing)
        self.assertIsNone(compose_purse(engines, exposures,
                                        (FENCED_TRANSFER,)).crossing)

    def test_a_pooled_system_declares_no_fence_so_nothing_crosses(self):
        self.assertFalse(crosses(CROSSING_TRANSFER, POOLED))
        self.assertTrue(crosses(CROSSING_TRANSFER, EMPIRICAL_FENCE))


class GrammarTests(unittest.TestCase):

    def test_the_registry_is_well_typed_and_unique(self):
        names = [s.name for s in REGISTRY]
        self.assertEqual(len(names), len(set(names)))
        self.assertEqual(len(REGISTRY), 13)

    def test_a_judge_reading_an_undeclared_table_is_withheld(self):
        from src.grammar import Footprint, ObjectionType

        leaky = ObjectionType("leaky", Footprint((), ("region",)),
                              lambda a, g: bool(a.read("liabilities")))
        verdict = judge(leaky, {"region": {}, "liabilities": {"x": 1}}, Grounds("g", {}))
        self.assertFalse(verdict.accepted)
        self.assertIsNone(verdict.upheld)

    def test_a_judge_that_raises_is_recorded_as_failing(self):
        from src.grammar import Footprint, ObjectionType

        def boom(access, grounds):
            raise RuntimeError("no")

        broken = ObjectionType("broken", Footprint((), ("region",)), boom)
        verdict = judge(broken, {"region": {}}, Grounds("g", {}))
        self.assertFalse(verdict.accepted)
        self.assertIsNone(verdict.upheld)

    def test_the_computed_classification_splits_every_legacy_family(self):
        self.assertEqual(len(CATALOG), 12)
        self.assertEqual(len(footprint_classes(CATALOG)), 10)
        self.assertEqual(len(evidence_classes(CATALOG)), 9)
        self.assertEqual(len(legacy_classes(CATALOG)), 4)
        self.assertEqual(len(splits_against_legacy(CATALOG)), 4)

    def test_ablation_reports_which_objections_lose_their_judgement(self):
        tables = {"region": {"infeasible": True}}
        grounds = {"exposure": Grounds("g:e", {})}
        result = ablate(CATALOG, tables, grounds, "region")
        self.assertIn("exposure", result.became_unavailable)


if __name__ == "__main__":
    unittest.main()
