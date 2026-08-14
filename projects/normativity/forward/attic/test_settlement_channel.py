"""WP-4: the funded empirical channel, constructed and exercised."""

from __future__ import annotations

import unittest
from dataclasses import replace
from fractions import Fraction as Q

from src.grammar import CATALOG_BY_ID, judge_objection
from src.leverage_interval import Book, Endorsement, Language
from src.settlement_channel import (
    CHANNEL_OWNER,
    THERMOMETER_A,
    THERMOMETER_B,
    WORLD,
    BridgeWarrant,
    Inference,
    WorldInstrument,
    adequacy_implies_no_missed_deadline,
    common_source_grounds,
    constrain,
    constructed_channel,
    execute,
    executor_cannot_read_the_book,
    grounding_evidence,
    observation_procedure,
    pin_has_no_answerability_columns,
    pinned,
    probe_blackout_grounds,
    request_is_directional,
    resolve,
    ripeness_gate,
    run_request,
    serve_earliest_deadline_first,
    settlement_request,
    stopping_is_outcome_independent,
    stopping_rule_is_precommitted,
    toll_missed_horizon,
)
from src.settlement_interface import (
    AdmittedQuery,
    DocketFacts,
    Pin,
    Position,
    Procedure,
    adequacy_inequality,
    report_variable,
)

CHANNEL = constructed_channel()


class RequestKeyTests(unittest.TestCase):
    """A key names a question; the type is the enforcement."""

    def test_the_constructed_request_is_not_directional(self):
        self.assertFalse(request_is_directional(CHANNEL["request"],
                                                THERMOMETER_A.outcome_space))

    def test_a_pin_carries_no_answerability_column(self):
        self.assertTrue(pin_has_no_answerability_columns())

    def test_a_request_cannot_be_scheduled_before_it_is_made(self):
        with self.assertRaises(ValueError):
            settlement_request("X", THERMOMETER_A, "funder:a", 3, 1, Q(1), "r:bad")


class ExecutionTests(unittest.TestCase):
    """Request, scheduled execution, pin."""

    def test_the_executor_cannot_see_the_book_or_the_purse(self):
        """The faithfulness path is unwritable in this signature.

        A disclosure about this implementation, not a proof of the axiom.
        """
        self.assertTrue(executor_cannot_read_the_book())

    def test_the_pin_reports_what_the_world_returned(self):
        outcome = CHANNEL["outcome"]
        self.assertIsNotNone(outcome.pin)
        self.assertEqual(outcome.pin.value, "warm")
        self.assertEqual(outcome.pin.variable_id,
                         report_variable("proc:thermometer-a", 1))
        self.assertFalse(outcome.missed_horizon)

    def test_a_value_outside_the_declared_outcome_space_is_refused(self):
        with self.assertRaises(ValueError):
            execute(THERMOMETER_A, 1, {("proc:thermometer-a", 1): "tepid"})

    def test_a_silent_world_past_the_horizon_is_a_missed_horizon(self):
        request = settlement_request(
            report_variable("proc:thermometer-a", 1), THERMOMETER_A, "funder:a", 0,
            1, Q(1), "r:silent")
        outcome = run_request(request, THERMOMETER_A, {}, 9)
        self.assertIsNone(outcome.pin)
        self.assertTrue(outcome.missed_horizon)

    def test_the_record_form_carries_the_execution_back(self):
        recorded = pinned(CHANNEL["outcome"])
        self.assertEqual(recorded.executed_date, 1)
        self.assertEqual(recorded.pinned_variable,
                         CHANNEL["outcome"].pin.variable_id)

    def test_a_procedure_needs_at_least_two_outcomes_to_settle_anything(self):
        with self.assertRaises(ValueError):
            observation_procedure("proc:x", ("only",), 1, CHANNEL_OWNER)


class DownstreamEffectTests(unittest.TestCase):
    """Constrain, pay, ground."""

    def setUp(self):
        variable = report_variable("proc:thermometer-a", 1)
        self.variable = variable
        self.pin = CHANNEL["outcome"].pin
        self.language = Language(("hot", "mild"),
                                 {variable: ("hot",), "H": ("hot",)})
        self.book = Book(1, ())

    def test_a_pin_constrains_the_region_permanently(self):
        before = constrain(self.language, self.book, (), {}, "H")
        after = constrain(self.language, self.book, (self.pin,),
                          {"warm": Q(1), "cold": Q(0)}, "H")
        self.assertEqual((before.lower, before.upper), (Q(0), Q(1)))
        self.assertEqual((after.lower, after.upper), (Q(1), Q(1)))

    def test_a_pin_pays_the_instruments_referencing_it(self):
        instrument = WorldInstrument("i:1", self.variable, "holder", "counterparty",
                                     {"warm": Q(3), "cold": Q(0)})
        transfers = resolve((instrument,), self.pin)
        self.assertEqual(len(transfers), 1)
        self.assertEqual(transfers[0].amount, Q(3))
        self.assertEqual(transfers[0].to_account, "holder")

    def test_an_instrument_on_another_variable_does_not_resolve(self):
        instrument = WorldInstrument("i:2", "X[other@1]", "holder", "counterparty",
                                     {"warm": Q(3)})
        self.assertEqual(resolve((instrument,), self.pin), ())

    def test_a_pin_grounds_evidence_through_an_endorsed_bridge(self):
        warrant = BridgeWarrant("w", self.variable, "the room is hot", "supports")
        grounds = grounding_evidence(self.pin, "the room is hot", warrant, "g:1")
        self.assertIsNotNone(grounds)
        self.assertEqual(grounds.payload["value"], "warm")
        self.assertEqual(grounds.payload["warrant_id"], "w")

    def test_an_unendorsed_bridge_grounds_nothing(self):
        warrant = BridgeWarrant("w", self.variable, "the room is hot", "supports",
                                endorsed=False)
        self.assertIsNone(
            grounding_evidence(self.pin, "the room is hot", warrant, "g:2"))


class ClockDisciplineTests(unittest.TestCase):

    def setUp(self):
        self.procedures = CHANNEL["procedures"]

    def test_an_unripe_query_is_refused_without_liability(self):
        query = AdmittedQuery("q:rush", 0, 1, ("proc:thermometer-a",), Q(1))
        verdict = ripeness_gate(query, self.procedures)
        self.assertFalse(verdict.ripe)
        self.assertEqual(verdict.liability, Q(0))
        self.assertIn("without liability", verdict.detail)

    def test_a_reachable_query_is_ripe(self):
        query = AdmittedQuery("q:fine", 0, 8, ("proc:thermometer-a",), Q(1))
        self.assertTrue(ripeness_gate(query, self.procedures).ripe)

    def test_a_query_on_the_rateless_channel_is_admitted_and_tolled(self):
        logical = Procedure("proc:decide", "logical", ("proved", "refuted"),
                            CHANNEL_OWNER)
        query = AdmittedQuery("q:deep", 0, 1, ("proc:decide",), Q(1))
        verdict = ripeness_gate(query, {"proc:decide": logical})
        self.assertTrue(verdict.ripe)
        self.assertEqual(verdict.liability, Q(0))
        self.assertIn("tolled", verdict.detail)

    def test_a_missed_horizon_tolls_and_charges_the_book_nothing(self):
        query = AdmittedQuery("q:late", 0, 9, ("proc:thermometer-a",), Q(1))
        record = toll_missed_horizon(query, THERMOMETER_A, 5)
        self.assertIsNotNone(record)
        self.assertEqual(record.tolled_dates, 3)
        self.assertFalse(record.chargeable_to_book)

    def test_a_horizon_met_tolls_nothing(self):
        query = AdmittedQuery("q:ok", 0, 9, ("proc:thermometer-a",), Q(1))
        self.assertIsNone(toll_missed_horizon(query, THERMOMETER_A, 2))


class AdequacyTests(unittest.TestCase):
    """C3 in general form, proved for the constructed channel."""

    def test_the_adequate_channel_meets_every_deadline(self):
        adequate, met = adequacy_implies_no_missed_deadline(CHANNEL["engine"],
                                                            CHANNEL["record"])
        self.assertTrue(adequate)
        self.assertTrue(met)

    def test_a_deadline_too_tight_for_the_horizon_fails_and_is_missed(self):
        tight = constructed_channel(deadline=4)
        adequate, met = adequacy_implies_no_missed_deadline(tight["engine"],
                                                            tight["record"])
        self.assertFalse(adequate)
        self.assertFalse(met)

    def test_the_violation_names_both_inequalities(self):
        tight = constructed_channel(deadline=4)
        obstructions = " ".join(adequacy_inequality(tight["engine"],
                                                    tight["record"]))
        self.assertIn("per-query adequacy inequality", obstructions)
        self.assertIn("window", obstructions)

    def test_capacity_alone_can_break_adequacy(self):
        """Two queries adequate one at a time, jointly impossible."""
        record = CHANNEL["record"]
        docket = DocketFacts(capacity=Q(1), queries=(
            AdmittedQuery("q:1", 0, 4, ("proc:thermometer-a",), Q(2), True),
            AdmittedQuery("q:2", 0, 4, ("proc:thermometer-a",), Q(2), True)))
        crowded = replace(record, docket=docket)
        obstructions = adequacy_inequality(CHANNEL["engine"], crowded)
        self.assertTrue(any("window" in o for o in obstructions))
        outcomes = serve_earliest_deadline_first(CHANNEL["engine"], docket, 6)
        self.assertFalse(all(o.met for o in outcomes))

    def test_service_is_earliest_deadline_first_and_respects_release(self):
        outcomes = serve_earliest_deadline_first(CHANNEL["engine"],
                                                 CHANNEL["record"].docket, 6)
        for outcome in outcomes:
            with self.subTest(query=outcome.query_id):
                self.assertGreaterEqual(outcome.completed, outcome.release)
                self.assertTrue(outcome.met)


class ConductTests(unittest.TestCase):

    def test_a_precommitted_rule_is_a_checkable_property_of_the_request(self):
        self.assertTrue(stopping_rule_is_precommitted(pinned(CHANNEL["outcome"])))

    def test_a_stop_that_moved_is_not_precommitted(self):
        moved = replace(pinned(CHANNEL["outcome"]), executed_date=4)
        self.assertFalse(stopping_rule_is_precommitted(moved))

    def test_the_stop_date_does_not_depend_on_what_the_world_returned(self):
        """The neutrality content, checked by replay under opposite worlds."""
        request = CHANNEL["request"]
        worlds = ({("proc:thermometer-a", 1): "warm"},
                  {("proc:thermometer-a", 1): "cold"})
        self.assertTrue(
            stopping_is_outcome_independent(request, THERMOMETER_A, worlds, 6))

    def test_the_blackout_objection_fires_on_an_inside_position(self):
        request = pinned(CHANNEL["outcome"])
        position = Position("funder:a", request.key.target, 1)
        grounds = probe_blackout_grounds(request, (position,), "g:blackout")
        self.assertIsNotNone(grounds)
        self.assertEqual(grounds.payload["window"], (0, 1))

    def test_the_control_does_not_fire(self):
        """Outside the window, and by another actor: neither is the objection."""
        request = pinned(CHANNEL["outcome"])
        outside = Position("funder:a", request.key.target, 5)
        other = Position("funder:b", request.key.target, 1)
        stale = Position("funder:a", request.key.target, 1, fresh=False)
        for position in (outside, other, stale):
            with self.subTest(position=position.actor_id):
                self.assertIsNone(
                    probe_blackout_grounds(request, (position,), "g:none"))

    def test_the_blackout_judge_accepts_the_grounds_under_its_footprint(self):
        request = pinned(CHANNEL["outcome"])
        position = Position("funder:a", request.key.target, 1)
        grounds = probe_blackout_grounds(request, (position,), "g:blackout")
        tables = {
            "settlement.requests": {request.request_id: {
                "funder_id": request.key.funder_id, "target": request.key.target}},
            "positions": {"p:1": {"actor_id": position.actor_id,
                                  "target": position.target,
                                  "date": position.date, "fresh": True}},
        }
        verdict = judge_objection(CATALOG_BY_ID["probe-blackout"], tables, grounds)
        self.assertTrue(verdict.accepted, verdict.obstructions)
        self.assertTrue(verdict.upheld)

    def test_one_purse_funding_every_premise_grounds_the_common_source(self):
        pins = (
            Pin("X[a@1]", "proc:thermometer-a", 1, "warm", ("funder:a",)),
            Pin("X[b@1]", "proc:thermometer-b", 1, "cold", ("funder:a",)),
        )
        inference = Inference("the room is hot", ("X[a@1]", "X[b@1]"))
        grounds = common_source_grounds(inference, pins, "g:common")
        self.assertIsNotNone(grounds)
        self.assertEqual(grounds.payload["common_funders"], ("funder:a",))

    def test_two_purses_do_not_ground_it(self):
        pins = (
            Pin("X[a@1]", "proc:thermometer-a", 1, "warm", ("funder:a",)),
            Pin("X[b@1]", "proc:thermometer-b", 1, "cold", ("funder:b",)),
        )
        inference = Inference("the room is hot", ("X[a@1]", "X[b@1]"))
        self.assertIsNone(common_source_grounds(inference, pins, "g:none"))

    def test_the_common_source_judge_accepts_under_its_footprint(self):
        pins = (
            Pin("X[a@1]", "proc:thermometer-a", 1, "warm", ("funder:a",)),
            Pin("X[b@1]", "proc:thermometer-b", 1, "cold", ("funder:a",)),
        )
        inference = Inference("the room is hot", ("X[a@1]", "X[b@1]"))
        grounds = common_source_grounds(inference, pins, "g:common")
        tables = {"settlement.pins": {
            pin.variable_id: {"funder_profile": pin.funder_profile} for pin in pins}}
        verdict = judge_objection(CATALOG_BY_ID["common-source"], tables, grounds)
        self.assertTrue(verdict.accepted, verdict.obstructions)
        self.assertTrue(verdict.upheld)


if __name__ == "__main__":
    unittest.main()
