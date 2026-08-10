from dataclasses import replace
from pathlib import Path
import re
import unittest

from src.answerability import (
    COMPLETION_RULES,
    EXAMPLES,
    SYSTEM_COVERAGE,
    SYSTEM_RIVALROUS,
    SYSTEMS,
    BoundaryDisposition,
    Carry,
    Cover,
    Discharge,
    Dispose,
    LedgerLog,
    FileObligation,
    FileResponse,
    Identify,
    Obligation,
    ObligationStatus,
    Refine,
    Reopen,
    Response,
    Suspend,
    compare_systems,
    compose_ledgers,
    compose_segments,
    example,
    historical_state,
    live_state,
    structural_adequacy,
    verify_ledger,
)


def _codes(report):
    return {o.code for o in report.obstructions}


class AnswerabilityLedgerTests(unittest.TestCase):
    # The ledger-completeness check moved to the consolidation, which now
    # owns the claim ledger and enforces coverage in its own runner.
    def test_example_a_illegitimate_co_discharge_is_blocked(self):
        log, versions = example("A")
        report = verify_ledger(log, transition_versions=versions)
        self.assertTrue(report.accepted, report.obstructions)
        # Both obligations share a carrier; only the covered one closes.
        self.assertEqual(sorted(report.closed), ["d:A"])
        self.assertEqual(report.open_ids, ("d:B",))
        self.assertEqual(report.live["d:B"].carrier, report.closed["d:A"].carrier)
        self.assertEqual(report.closed["d:A"].closure_kind, "discharge")
        # Trying to close d:B with d:A's edge is a typed rejection.
        laundered = LedgerLog("laundered", log.events + (
            Discharge("e:disc-B", 1, "d:B", "e:cover-A"),))
        verdict = verify_ledger(laundered)
        self.assertFalse(verdict.accepted)
        self.assertIn("ledger.implicit_co_discharge", _codes(verdict))

    def test_example_b_one_response_may_answer_two_obligations(self):
        report = verify_ledger(*[example("B")[0]], transition_versions=example("B")[1])
        self.assertTrue(report.accepted, report.obstructions)
        self.assertEqual(sorted(report.closed), ["d:A", "d:B"])
        self.assertEqual(report.open_ids, ())
        # One response, two independently certified edges, two dispositions.
        self.assertEqual(len({r for r, _, _ in report.coverage}), 1)
        self.assertEqual(len(report.coverage), 2)
        self.assertEqual(len({adequacy for _, _, adequacy in report.coverage}), 2)
        self.assertEqual(len({report.closed[i].closure_event for i in report.closed}), 2)

    def test_example_c_identification_by_carrier_merger_is_rejected(self):
        log, versions = example("C")
        report = verify_ledger(log, transition_versions=versions)
        self.assertFalse(report.accepted)
        self.assertIn("ledger.identification_by_carrier_merger", _codes(report))
        obstruction = next(o for o in report.obstructions
                           if o.code == "ledger.identification_by_carrier_merger")
        self.assertEqual(obstruction.obligation_ids, ("d:A", "d:B"))
        self.assertEqual(report.open_ids, ("d:A", "d:B"))

    def test_example_d_authorized_identification_keeps_both_dispositions(self):
        log, versions = example("D")
        report = verify_ledger(log, transition_versions=versions)
        self.assertTrue(report.accepted, report.obstructions)
        # Design choice: two obligations sharing one adequacy argument, each with
        # its own coverage edge and its own disposition record.
        self.assertEqual(sorted(report.closed), ["d:A", "d:B"])
        self.assertEqual(len(report.coverage), 2)
        self.assertEqual({adequacy for _, _, adequacy in report.coverage}, {"adequacy:shared"})
        self.assertEqual(len({report.closed[i].closure_event for i in report.closed}), 2)
        for identifier in ("d:A", "d:B"):
            self.assertEqual(report.closed[identifier].obligation.origin_event,
                             f"e:file-{identifier[-1]}")
        # Identification without a certificate is rejected.
        stripped = LedgerLog("stripped", tuple(
            replace(e, certificate="") if isinstance(e, Identify) else e
            for e in log.events))
        self.assertIn("ledger.identification_without_certificate",
                      _codes(verify_ledger(stripped)))

    def test_example_e_parent_needs_its_declared_completion_rule(self):
        log, _ = example("E")
        report = verify_ledger(log)
        self.assertFalse(report.accepted)
        self.assertIn("ledger.parent_discharged_early", _codes(report))
        self.assertIn("d:A", report.open_ids)
        self.assertEqual(sorted(report.closed), ["d:A1"])
        # Closing the second child satisfies the "all" rule and the parent closes.
        completed = LedgerLog("completed", log.events[:-1] + (
            Cover("e:cover-A2", 1, "r:1", "d:A2", "adequacy:A2", "auth:review"),
            Discharge("e:disc-A2", 1, "d:A2", "e:cover-A2"),
            Discharge("e:disc-parent", 1, "d:A", "e:cover-A"),
        ))
        finished = verify_ledger(completed)
        self.assertTrue(finished.accepted, finished.obstructions)
        self.assertEqual(sorted(finished.closed), ["d:A", "d:A1", "d:A2"])
        # Children record the parent in their lineage.
        self.assertIn("d:A", finished.closed["d:A1"].obligation.lineage)
        # Under "any", one child suffices; the rule is declared, not assumed.
        relaxed = LedgerLog("relaxed", tuple(
            replace(e, completion_rule="any") if isinstance(e, Refine) else e
            for e in log.events))
        self.assertTrue(verify_ledger(relaxed).accepted)
        self.assertIn("all", COMPLETION_RULES)

    def test_example_f_reopening_preserves_history(self):
        log, _ = example("F")
        report = verify_ledger(log)
        self.assertTrue(report.accepted, report.obstructions)
        self.assertEqual(report.open_ids, ("d:A",))
        self.assertEqual(report.live["d:A"].reopened, 1)
        self.assertIsNone(report.live["d:A"].closure_event)
        # The prior discharge is still in the log: history is not rewritten.
        self.assertTrue(any(isinstance(e, Discharge) for e in log.events))
        prefix = verify_ledger(log.prefix(1))
        self.assertEqual(sorted(prefix.closed), ["d:A"])
        # Reopening without a named undercutter is rejected.
        hollow = LedgerLog("hollow", tuple(
            replace(e, undercutter_ref="") if isinstance(e, Reopen) else e
            for e in log.events))
        self.assertIn("ledger.reopen_without_undercutter", _codes(verify_ledger(hollow)))

    def test_example_g_inexpressible_target_stays_owed(self):
        log, versions = example("G")
        report = verify_ledger(log, transition_versions=versions)
        self.assertTrue(report.accepted, report.obstructions)
        self.assertEqual(report.open_ids, ("d:A",))
        self.assertEqual(report.live["d:A"].status, ObligationStatus.SUSPENDED)
        self.assertEqual(report.live["d:A"].carrier, "legacy:claim:A")
        self.assertEqual(report.closed, {})

    def test_every_example_is_exercised(self):
        self.assertEqual(len(EXAMPLES), 7)
        for name in EXAMPLES:
            log, versions = example(name)
            self.assertTrue(log.events)
            verify_ledger(log, transition_versions=versions)

    # ---- transition and coverage conditions -------------------------------

    def test_a_response_is_not_a_discharge(self):
        obligation = Obligation("d:x", "justify", 0, "e:f", "auth:c", "claim:x")
        log = LedgerLog("bare", (
            FileObligation("e:f", 0, obligation),
            FileResponse("e:r", 0, Response("r:1", "justify", 0, "auth:filing")),
            Discharge("e:d", 0, "d:x", "e:missing"),
        ))
        report = verify_ledger(log)
        self.assertFalse(report.accepted)
        self.assertIn("ledger.discharge_without_coverage", _codes(report))
        self.assertEqual(report.open_ids, ("d:x",))

    def test_coverage_requires_kind_match_and_authorization(self):
        obligation = Obligation("d:x", "justify", 0, "e:f", "auth:c", "claim:x")
        base = (FileObligation("e:f", 0, obligation),
                FileResponse("e:r", 0, Response("r:1", "settle", 0, "auth:filing")))
        mismatched = LedgerLog("kind", base + (
            Cover("e:c", 0, "r:1", "d:x", "adequacy", "auth:review"),))
        self.assertIn("ledger.coverage_inadequate", _codes(verify_ledger(mismatched)))
        matched = (FileObligation("e:f", 0, obligation),
                   FileResponse("e:r", 0, Response("r:1", "justify", 0, "auth:filing")))
        unauthorized = LedgerLog("auth", matched + (
            Cover("e:c", 0, "r:1", "d:x", "adequacy", ""),))
        self.assertIn("ledger.coverage_unauthorized", _codes(verify_ledger(unauthorized)))
        no_certificate = LedgerLog("cert", matched + (
            Cover("e:c", 0, "r:1", "d:x", "", "auth:review"),))
        self.assertIn("ledger.coverage_inadequate", _codes(verify_ledger(no_certificate)))

    def test_adequacy_is_parametric(self):
        obligation = Obligation("d:x", "justify", 0, "e:f", "auth:c", "claim:x")
        log = LedgerLog("param", (
            FileObligation("e:f", 0, obligation),
            FileResponse("e:r", 0, Response("r:1", "justify", 0, "auth:filing")),
            Cover("e:c", 0, "r:1", "d:x", "adequacy:weak", "auth:review"),
            Discharge("e:d", 0, "d:x", "e:c"),
        ))
        self.assertTrue(verify_ledger(log).accepted)
        strict = lambda cover, obligation_, response: (
            structural_adequacy(cover, obligation_, response)
            and cover.adequacy_ref.endswith("strong"))
        self.assertFalse(verify_ledger(log, adequacy=strict).accepted)
        self.assertIn("ledger.coverage_inadequate", _codes(verify_ledger(log, adequacy=strict)))

    def test_open_obligation_must_be_disposed_at_a_transition(self):
        obligation = Obligation("d:x", "justify", 0, "e:f", "auth:c", "claim:x")
        stranded = LedgerLog("stranded", (FileObligation("e:f", 0, obligation),))
        report = verify_ledger(stranded, transition_versions=(1,))
        self.assertFalse(report.accepted)
        self.assertIn("ledger.no_boundary_disposition", _codes(report))
        # A coverage edge is not a disposition.
        response = FileResponse("e:r", 1, Response("r:1", "justify", 1, "auth:filing"))
        mentioned = LedgerLog("mentioned", stranded.events + (
            response, Cover("e:cov", 1, "r:1", "d:x", "adequacy", "auth:review")))
        self.assertIn("ledger.no_boundary_disposition",
                      _codes(verify_ledger(mentioned, transition_versions=(1,))))
        carried = LedgerLog("carried", stranded.events + (
            Carry("e:c", 1, "d:x", "claim:x-prime", "auth:migration"),
            BoundaryDisposition("e:bd", 1, "d:x", "continue", "auth:migration", ("e:c",))))
        self.assertTrue(verify_ledger(carried, transition_versions=(1,)).accepted)
        # Two top-level dispositions for one obligation is a conflict.
        conflicting = LedgerLog("conflicting", carried.events + (
            BoundaryDisposition("e:bd2", 1, "d:x", "terminal", "auth:migration"),))
        self.assertIn("ledger.conflicting_boundary_disposition",
                      _codes(verify_ledger(conflicting, transition_versions=(1,))))
        self.assertEqual(verify_ledger(carried).live["d:x"].carrier, "claim:x-prime")

    def test_terminal_disposition_requires_witness_and_authorization(self):
        obligation = Obligation("d:x", "justify", 0, "e:f", "auth:c", "claim:x")
        base = (FileObligation("e:f", 0, obligation),)
        good = LedgerLog("good", base + (
            Dispose("e:d", 1, "d:x", "loss", "witness:w", "auth:review"),))
        report = verify_ledger(good)
        self.assertTrue(report.accepted, report.obstructions)
        self.assertEqual(report.closed["d:x"].closure_kind, "loss")
        for bad in (Dispose("e:d", 1, "d:x", "loss", "", "auth:review"),
                    Dispose("e:d", 1, "d:x", "discharge", "w", "auth:review")):
            self.assertFalse(verify_ledger(LedgerLog("bad", base + (bad,))).accepted)

    def test_unauthorized_origin_is_rejected(self):
        naked = Obligation("d:x", "justify", 0, "e:f", "", "claim:x")
        report = verify_ledger(LedgerLog("naked", (FileObligation("e:f", 0, naked),)))
        self.assertFalse(report.accepted)
        self.assertIn("ledger.unauthorized_origin", _codes(report))

    def test_duplicate_obligation_identifiers_are_rejected(self):
        obligation = Obligation("d:x", "justify", 0, "e:1", "auth:c", "claim:x")
        twice = LedgerLog("twice", (FileObligation("e:1", 0, obligation),
                                    FileObligation("e:2", 1, obligation)))
        self.assertIn("ledger.duplicate_obligation_id", _codes(verify_ledger(twice)))

    # ---- composition and associativity ------------------------------------

    def test_composition_is_concatenation_and_associative(self):
        first, _ = example("A")
        obligation = Obligation("d:C", "justify", 2, "e:file-C", "auth:c", "claim:C")
        second = LedgerLog("seg2", (FileObligation("e:file-C", 2, obligation),))
        third = LedgerLog("seg3", (
            Dispose("e:dispose-C", 3, "d:C", "withdrawal", "w:1", "auth:review"),))
        left = compose_ledgers(compose_ledgers(first, second), third)
        right = compose_ledgers(first, compose_ledgers(second, third))
        self.assertEqual(left.events, right.events)
        left_report, right_report = verify_ledger(left), verify_ledger(right)
        self.assertEqual(live_state(left_report), live_state(right_report))
        self.assertEqual(historical_state(left_report), historical_state(right_report))
        self.assertTrue(left_report.accepted)
        self.assertEqual(sorted(left_report.closed), ["d:A", "d:C"])
        self.assertEqual(left_report.open_ids, ("d:B",))

    def test_live_and_historical_state_are_separated(self):
        log, _ = example("F")
        report = verify_ledger(log.prefix(1))
        self.assertEqual(live_state(report), {})
        self.assertEqual(list(historical_state(report)), ["d:A"])
        after = verify_ledger(log)
        self.assertEqual(list(live_state(after)), ["d:A"])
        self.assertEqual(historical_state(after), {})

    # ---- Gate 7 three-system comparison -----------------------------------

    def test_certified_coverage_is_stronger_than_rivalrous_witnesses(self):
        comparison = compare_systems()
        self.assertEqual(comparison.scenarios, 92)
        self.assertEqual(set(comparison.accepted), set(SYSTEMS))
        # System 1 accepts unsafe closures; systems 2 and 3 accept none.
        self.assertGreater(comparison.unsafe_accepted["burden-bit"], 0)
        self.assertEqual(comparison.unsafe_accepted[SYSTEM_RIVALROUS], 0)
        self.assertEqual(comparison.unsafe_accepted[SYSTEM_COVERAGE], 0)
        # System 3 accepts legitimate shared responses; system 2 accepts none.
        self.assertGreater(comparison.legitimate_shared_accepted[SYSTEM_COVERAGE], 0)
        self.assertEqual(comparison.legitimate_shared_accepted[SYSTEM_RIVALROUS], 0)
        self.assertGreater(comparison.accepted[SYSTEM_COVERAGE],
                           comparison.accepted[SYSTEM_RIVALROUS])
        self.assertTrue(comparison.strictly_more_expressive)
        self.assertTrue(comparison.equally_safe)
        self.assertTrue(comparison.expressiveness_witnesses)
        self.assertEqual(comparison.safety_witnesses, ())

    def test_comparison_is_deterministic(self):
        self.assertEqual(compare_systems(), compare_systems())


if __name__ == "__main__":
    unittest.main()


class AnswerabilityIndependenceTests(unittest.TestCase):
    def test_conservation_does_not_imply_frontier_coverage(self):
        """AD-X3: an obligation may be conserved while its carrier loses the target."""
        obligation = Obligation("d:x", "justify", 0, "e:f", "auth:c", "edge:original")
        log = LedgerLog("drift", (
            FileObligation("e:f", 0, obligation),
            Carry("e:c", 1, "d:x", "edge:unrelated", "auth:migration"),
            BoundaryDisposition("e:bd", 1, "d:x", "continue", "auth:migration", ("e:c",)),
        ))
        report = verify_ledger(log, transition_versions=(1,))
        # Ledger conservation holds: the obligation is still open and accounted for.
        self.assertTrue(report.accepted, report.obstructions)
        self.assertEqual(report.open_ids, ("d:x",))
        # Yet the carrier bears no declared relation to the original target, so
        # nothing here supplies the prefix challenge-frontier condition.
        self.assertEqual(report.live["d:x"].carrier, "edge:unrelated")
        self.assertNotEqual(report.live["d:x"].carrier,
                            report.live["d:x"].obligation.carrier)


class SegmentCompositionTests(unittest.TestCase):
    """Gate 1.4: compatibility, not free-monoid concatenation, is the content."""

    def _segment(self, tag, identifier, version):
        obligation = Obligation(identifier, "justify", version, f"e:file-{tag}",
                                "auth:c", f"claim:{tag}")
        return LedgerLog(f"seg:{tag}", (
            FileObligation(f"e:file-{tag}", version, obligation),))

    def test_compatible_segments_compose_into_an_accepted_segment(self):
        first = self._segment("a", "d:a", 0)
        second = LedgerLog("seg:b", (
            Dispose("e:dispose-a", 1, "d:a", "withdrawal", "w:1", "auth:review"),))
        composition = compose_segments(first, second)
        self.assertTrue(composition.accepted, composition.obstructions)
        report = verify_ledger(composition.composed)
        self.assertTrue(report.accepted, report.obstructions)
        self.assertEqual(sorted(report.closed), ["d:a"])
        # The composed events are exactly the concatenation, in order.
        self.assertEqual(composition.composed.events, first.events + second.events)

    def test_identifier_collision_across_the_seam_is_rejected(self):
        first = self._segment("a", "d:a", 0)
        clash = self._segment("a", "d:a", 1)
        composition = compose_segments(first, clash)
        self.assertFalse(composition.accepted)
        codes = {o.code for o in composition.obstructions}
        self.assertIn("ledger.segment_identifier_collision", codes)

    def test_version_regression_across_the_seam_is_rejected(self):
        first = self._segment("a", "d:a", 3)
        second = LedgerLog("seg:b", (
            Dispose("e:dispose-a", 1, "d:a", "withdrawal", "w:1", "auth:review"),))
        composition = compose_segments(first, second)
        self.assertFalse(composition.accepted)
        self.assertIn("ledger.segment_version_regression",
                      {o.code for o in composition.obstructions})
        # And the fold itself rejects the out-of-order append.
        self.assertIn("ledger.version_out_of_order",
                      _codes(verify_ledger(composition.composed)))

    def test_acting_on_an_obligation_the_first_segment_closed_is_rejected(self):
        first = self._segment("a", "d:a", 0)
        first = LedgerLog("seg:a", first.events + (
            Dispose("e:dispose-a", 0, "d:a", "withdrawal", "w:1", "auth:review"),))
        second = LedgerLog("seg:b", (
            Carry("e:carry-a", 1, "d:a", "claim:new", "auth:migration"),))
        composition = compose_segments(first, second)
        self.assertFalse(composition.accepted)
        self.assertIn("ledger.segment_acts_on_closed_obligation",
                      {o.code for o in composition.obstructions})

    def test_dangling_reference_is_rejected(self):
        first = self._segment("a", "d:a", 0)
        second = LedgerLog("seg:b", (
            Carry("e:carry-z", 1, "d:z", "claim:new", "auth:migration"),))
        composition = compose_segments(first, second)
        self.assertFalse(composition.accepted)
        self.assertIn("ledger.segment_dangling_reference",
                      {o.code for o in composition.obstructions})

    def test_composition_is_associative_on_compatible_segments(self):
        a = self._segment("a", "d:a", 0)
        b = self._segment("b", "d:b", 1)
        c = LedgerLog("seg:c", (
            Dispose("e:dispose-a", 2, "d:a", "withdrawal", "w:1", "auth:review"),
            Dispose("e:dispose-b", 2, "d:b", "withdrawal", "w:2", "auth:review"),))
        left = compose_segments(compose_segments(a, b).composed, c)
        right = compose_segments(a, compose_segments(b, c).composed)
        self.assertTrue(left.accepted and right.accepted)
        self.assertEqual(left.composed.events, right.composed.events)
        self.assertEqual(live_state(verify_ledger(left.composed)),
                         live_state(verify_ledger(right.composed)))
        self.assertEqual(historical_state(verify_ledger(left.composed)),
                         historical_state(verify_ledger(right.composed)))
        self.assertTrue(verify_ledger(left.composed).accepted)


class CompositionContractTests(unittest.TestCase):
    """The four clauses `compose_segments` actually establishes."""

    def test_contract_reports_all_four_clauses(self):
        obligation = Obligation("d:a", "justify", 0, "e:file", "auth:c", "claim:a")
        first = LedgerLog("seg:a", (FileObligation("e:file", 0, obligation),))
        second = LedgerLog("seg:b", (
            Dispose("e:dispose", 1, "d:a", "withdrawal", "w:1", "auth:review"),))
        composition = compose_segments(first, second)
        self.assertTrue(composition.first_accepted)
        self.assertTrue(composition.compatible)
        self.assertTrue(composition.second_accepted_under_state)
        self.assertTrue(composition.composite_accepted)
        self.assertTrue(composition.accepted)

    def test_an_invalid_second_segment_is_not_hidden_by_a_valid_first(self):
        obligation = Obligation("d:a", "justify", 0, "e:file", "auth:c", "claim:a")
        first = LedgerLog("seg:a", (FileObligation("e:file", 0, obligation),))
        # The second segment disposes with no witness: valid seam, invalid content.
        second = LedgerLog("seg:b", (
            Dispose("e:dispose", 1, "d:a", "withdrawal", "", "auth:review"),))
        composition = compose_segments(first, second)
        self.assertTrue(composition.first_accepted)
        self.assertFalse(composition.second_accepted_under_state)
        self.assertFalse(composition.composite_accepted)
        self.assertFalse(composition.accepted)
        codes = {o.code for o in composition.obstructions}
        self.assertIn("ledger.second_segment_rejected_under_state", codes)
        self.assertIn("ledger.composite_not_accepted", codes)
