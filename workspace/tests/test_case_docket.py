from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path
import re
import unittest

from src.answerability import (
    BoundaryDisposition, Carry, FileObligation, LedgerLog, verify_ledger)
from src.case_docket import (
    BASIS_DEFAULT, BASIS_MERITS, AdjudicationReport, CredalInterval, MeritsCertificate,
    ProcedureSchedule, Query, RetrospectiveAmendment, Ruling, adjudicate, certify_merits,
    decision_obligation, default_disposition,
    merits_direction, merits_ledger_events)

SCHEDULE = ProcedureSchedule("ct:liable", 1, "target:", Q(3, 4), "liable", "not-liable",
                             "not-liable", Q(1, 10), Q(1, 20), "auth:procedure")
QUERY = Query("q:1", "case:1", "ct:liable", 1, "target:x")
EMPTY = CredalInterval(1, "target:x", Q(0), Q(1))
POSITIVE = CredalInterval(1, "target:x", Q(4, 5), Q(9, 10))
NEGATIVE = CredalInterval(1, "target:x", Q(1, 10), Q(1, 2))


def _run(interval, rulings, certificates, *, queries=(QUERY,), schedules=(SCHEDULE,),
         horizon=0, amendments=(), ledger=None):
    return adjudicate(list(queries), list(schedules), {"target:x": interval},
                      list(rulings), list(certificates),
                      horizon_step=horizon, amendments=amendments, ledger=ledger)


def _codes(report):
    return {o.code for o in report.obstructions}


class CaseDocketTests(unittest.TestCase):
    # The ledger-completeness check moved to the consolidation, which now
    # owns the claim ledger and enforces coverage in its own runner.
    def test_empty_book_offers_no_merits(self):
        self.assertIsNone(merits_direction(EMPTY, SCHEDULE.threshold))
        self.assertIsNone(certify_merits(QUERY, SCHEDULE, EMPTY, "cert:x"))

    def test_empty_book_default_closes_procedurally_with_liability(self):
        ruling = Ruling("ru:1", "q:1", "not-liable", BASIS_DEFAULT, (), 1, 1)
        report = _run(EMPTY, [ruling], [])
        self.assertTrue(report.accepted, report.obstructions)
        self.assertEqual(report.open_decisions, ())
        self.assertEqual(report.total_liability, SCHEDULE.default_tariff)
        self.assertEqual([e.kind for e in report.liabilities], ["default"])

    def test_empty_book_decline_keeps_the_obligation_open_and_costly(self):
        report = _run(EMPTY, [], [], horizon=2)
        self.assertTrue(report.accepted, report.obstructions)
        self.assertEqual(report.open_decisions, ("q:1",))
        self.assertEqual(report.total_liability, 2 * SCHEDULE.refusal_tariff)
        self.assertEqual([e.step for e in report.liabilities], [0, 1])
        # A ruled query accrues no refusal charge over the same horizon.
        ruling = Ruling("ru:1", "q:1", "not-liable", BASIS_DEFAULT, (), 1, 1)
        ruled = _run(EMPTY, [ruling], [], horizon=1)
        self.assertTrue(ruled.accepted, ruled.obstructions)
        self.assertEqual([e.kind for e in ruled.liabilities], ["default"])

    def test_positive_and_negative_merits(self):
        positive = certify_merits(QUERY, SCHEDULE, POSITIVE, "cert:p")
        self.assertEqual(positive.direction, "positive")
        report = _run(POSITIVE, [Ruling("ru:p", "q:1", "liable", BASIS_MERITS,
                                        ("cert:p",), 1, 1)], [positive])
        self.assertTrue(report.accepted, report.obstructions)
        self.assertEqual(report.total_liability, Q(0))
        negative = certify_merits(QUERY, SCHEDULE, NEGATIVE, "cert:n")
        self.assertEqual(negative.direction, "negative")
        self.assertTrue(_run(NEGATIVE, [Ruling("ru:n", "q:1", "not-liable", BASIS_MERITS,
                                               ("cert:n",), 1, 1)], [negative]).accepted)
        # An indeterminate interval straddling the threshold certifies nothing.
        straddle = CredalInterval(1, "target:x", Q(7, 10), Q(4, 5))
        self.assertIsNone(merits_direction(straddle, SCHEDULE.threshold))

    # CD-J2: unsupported merits.
    def test_unsupported_merits_is_rejected_under_every_mutation(self):
        good = certify_merits(QUERY, SCHEDULE, POSITIVE, "cert:p")
        base = Ruling("ru:p", "q:1", "liable", BASIS_MERITS, ("cert:p",), 1, 1)
        self.assertTrue(_run(POSITIVE, [base], [good]).accepted)
        mutations = {
            "wrong interval": (EMPTY, [base], [good]),
            "wrong threshold": (POSITIVE, [base], [replace(good, threshold=Q(1, 2))]),
            "wrong target": (POSITIVE, [base], [replace(good, target="target:other")]),
            "wrong book version": (POSITIVE, [base], [replace(good, book_version=9)]),
            "wrong query": (POSITIVE, [base], [replace(good, query_id="q:2")]),
            "forged id": (POSITIVE, [replace(base, certificate_ids=("cert:none",))], []),
            "merits on default": (POSITIVE, [replace(base, certificate_ids=())], []),
            "verdict mismatch": (POSITIVE, [replace(base, verdict="not-liable")], [good]),
        }
        for label, (interval, rulings, certificates) in mutations.items():
            report = _run(interval, rulings, certificates)
            self.assertFalse(report.accepted, label)
            self.assertTrue(report.obstructions, label)
        # A stale schedule version on the ruling is rejected too.
        self.assertIn("docket.stale_schedule",
                      _codes(_run(POSITIVE, [replace(base, bound_schedule_version=2)],
                                  [good])))

    # CD-J3: default non-laundering.
    def test_a_default_never_becomes_substantive_support(self):
        first = Ruling("ru:d", "q:1", "not-liable", BASIS_DEFAULT, (), 1, 1)
        report = _run(EMPTY, [first], [])
        self.assertTrue(report.accepted)
        # The default alters no interval and creates no coverage edge.
        self.assertEqual(report.rulings[0].certificate_ids, ())
        self.assertEqual(merits_direction(EMPTY, SCHEDULE.threshold), None)
        # A default cannot be dressed as a certificate: the verifier recomputes
        # the direction from the interval the book actually supplied.
        laundered = MeritsCertificate("ru:d", "q:2", "target:x", 1, 1, EMPTY,
                                      Q(3, 4), "negative")
        second = Query("q:2", "case:2", "ct:liable", 1, "target:x")
        report = _run(EMPTY, [Ruling("ru:2", "q:2", "not-liable", BASIS_MERITS,
                                     ("ru:d",), 1, 1)], [laundered],
                      queries=(QUERY, second))
        self.assertFalse(report.accepted)
        self.assertIn("docket.unsupported_merits", _codes(report))
        # A default citing a certificate at all is rejected.
        self.assertIn("docket.default_citing_certificate",
                      _codes(_run(EMPTY, [replace(first, certificate_ids=("cert:p",))], [])))
        # A default must issue the bound fallback verdict.
        self.assertIn("docket.default_not_fallback",
                      _codes(_run(EMPTY, [replace(first, verdict="liable")], [])))

    # CD-J4: prospective procedure.
    def test_procedure_changes_are_prospective(self):
        relaxed = replace(SCHEDULE, schedule_version=2, threshold=Q(1, 2))
        interval = CredalInterval(1, "target:x", Q(3, 5), Q(3, 5))
        wanted = MeritsCertificate("cert:r", "q:1", "target:x", 1, 2, interval,
                                   Q(1, 2), "positive")
        # The old query stays bound to version 1, under which 3/5 < 3/4.
        report = _run(interval, [Ruling("ru:r", "q:1", "liable", BASIS_MERITS,
                                        ("cert:r",), 1, 2)], [wanted],
                      schedules=(SCHEDULE, relaxed))
        self.assertFalse(report.accepted)
        self.assertIn("docket.stale_schedule", _codes(report))
        # A new query filed under version 2 is governed by version 2.
        fresh = Query("q:2", "case:2", "ct:liable", 2, "target:x")
        fresh_certificate = MeritsCertificate("cert:f", "q:2", "target:x", 1, 2,
                                              interval, Q(1, 2), "positive")
        self.assertTrue(_run(interval, [Ruling("ru:f", "q:2", "liable", BASIS_MERITS,
                                               ("cert:f",), 1, 2)], [fresh_certificate],
                             queries=(fresh,), schedules=(SCHEDULE, relaxed)).accepted)
        # An authorized retrospective amendment rebinds the old query; an
        # unauthorized one does not.
        authorized = RetrospectiveAmendment("am:1", "q:1", 1, 2, "auth:review",
                                            "liability:disclosed")
        self.assertTrue(_run(interval, [Ruling("ru:r", "q:1", "liable", BASIS_MERITS,
                                               ("cert:r",), 1, 2)], [wanted],
                             schedules=(SCHEDULE, relaxed),
                             amendments=(authorized,)).accepted)
        hollow = replace(authorized, authorization="")
        report = _run(interval, [Ruling("ru:r", "q:1", "liable", BASIS_MERITS,
                                        ("cert:r",), 1, 2)], [wanted],
                      schedules=(SCHEDULE, relaxed), amendments=(hollow,))
        self.assertFalse(report.accepted)
        self.assertIn("docket.unauthorized_retrospective_amendment", _codes(report))

    # Bridge to the answerability ledger.
    def test_merits_path_discharges_the_decision_obligation(self):
        obligation = decision_obligation(QUERY, "e:file", 0)
        certificate = certify_merits(QUERY, SCHEDULE, POSITIVE, "cert:p")
        ledger = LedgerLog("bridge", (FileObligation("e:file", 0, obligation),)
                           + merits_ledger_events(QUERY, certificate, 1, "auth:review"))
        ledger_report = verify_ledger(ledger, transition_versions=(1,))
        self.assertTrue(ledger_report.accepted, ledger_report.obstructions)
        self.assertEqual(sorted(ledger_report.closed), ["d:q:1"])
        report = _run(POSITIVE, [Ruling("ru:p", "q:1", "liable", BASIS_MERITS,
                                        ("cert:p",), 1, 1)], [certificate], ledger=ledger)
        self.assertTrue(report.accepted, report.obstructions)

    def test_default_path_closes_procedurally_not_substantively(self):
        obligation = decision_obligation(QUERY, "e:file", 0)
        dispose, boundary = default_disposition(
            QUERY, "e:default", 1, "auth:procedure", ruling_id="ru:d",
            fallback_verdict=SCHEDULE.fallback_verdict)
        ledger = LedgerLog("default", (FileObligation("e:file", 0, obligation),
                                       dispose, boundary))
        ledger_report = verify_ledger(ledger, transition_versions=(1,))
        self.assertTrue(ledger_report.accepted, ledger_report.obstructions)
        self.assertEqual(boundary.outcome, "procedural")
        # No coverage edge exists: nothing was answered on the merits.
        self.assertEqual(ledger_report.coverage, ())
        self.assertEqual(ledger_report.closed["d:q:1"].closure_kind, "procedural")

    def test_ruling_without_ledger_disposition_is_rejected(self):
        obligation = decision_obligation(QUERY, "e:file", 0)
        ledger = LedgerLog("open", (FileObligation("e:file", 0, obligation),))
        report = _run(EMPTY, [Ruling("ru:d", "q:1", "not-liable", BASIS_DEFAULT, (), 1, 1)],
                      [], ledger=ledger)
        self.assertFalse(report.accepted)
        self.assertIn("docket.ruling_without_ledger_disposition", _codes(report))

    def test_ledger_closed_without_a_ruling_is_rejected(self):
        obligation = decision_obligation(QUERY, "e:file", 0)
        dispose, boundary = default_disposition(
            QUERY, "e:default", 1, "auth:procedure", ruling_id="ru:d",
            fallback_verdict=SCHEDULE.fallback_verdict)
        ledger = LedgerLog("closed", (FileObligation("e:file", 0, obligation),
                                      dispose, boundary))
        report = _run(EMPTY, [], [], ledger=ledger)
        self.assertFalse(report.accepted)
        self.assertIn("docket.ledger_closed_without_ruling", _codes(report))

    def test_migration_retargets_the_obligation_and_keeps_query_identity(self):
        obligation = decision_obligation(QUERY, "e:file", 0)
        ledger = LedgerLog("migrated", (
            FileObligation("e:file", 0, obligation),
            Carry("e:carry", 1, "d:q:1", "target:x-refined", "auth:migration"),
            BoundaryDisposition("e:bd", 1, "d:q:1", "continue", "auth:migration",
                                ("e:carry",))))
        ledger_report = verify_ledger(ledger, transition_versions=(1,))
        self.assertTrue(ledger_report.accepted, ledger_report.obstructions)
        self.assertEqual(ledger_report.live["d:q:1"].carrier, "target:x-refined")
        # The query identity and its bound schedule are untouched.
        report = _run(EMPTY, [], [], horizon=1, ledger=ledger)
        self.assertTrue(report.accepted, report.obstructions)
        self.assertEqual(report.open_decisions, ("q:1",))

    def test_two_claim_types_on_one_case(self):
        other = ProcedureSchedule("ct:duty", 1, "target:", Q(1, 2), "owed", "not-owed",
                                  "not-owed", Q(1, 5), Q(1, 20), "auth:procedure")
        second = Query("q:2", "case:1", "ct:duty", 1, "target:x")
        interval = CredalInterval(1, "target:x", Q(3, 5), Q(3, 5))
        # The same interval yields opposite verdicts under the two claim types:
        # 3/5 clears 1/2 but falls short of 3/4.
        duty = certify_merits(second, other, interval, "cert:2")
        liable = certify_merits(QUERY, SCHEDULE, interval, "cert:1")
        self.assertEqual(duty.direction, "positive")
        self.assertEqual(liable.direction, "negative")
        report = adjudicate(
            [QUERY, second], [SCHEDULE, other], {"target:x": interval},
            [Ruling("ru:1", "q:1", "not-liable", BASIS_MERITS, ("cert:1",), 1, 1),
             Ruling("ru:2", "q:2", "owed", BASIS_MERITS, ("cert:2",), 1, 1)],
            [liable, duty])
        self.assertTrue(report.accepted, report.obstructions)
        self.assertEqual(report.total_liability, Q(0))

    def test_malformed_inputs_are_rejected(self):
        self.assertFalse(replace(SCHEDULE, threshold=Q(0)).well_formed())
        self.assertFalse(replace(SCHEDULE, threshold=Q(1)).well_formed())
        self.assertFalse(CredalInterval(1, "t", Q(3, 4), Q(1, 2)).well_formed())
        self.assertFalse(CredalInterval(1, "t", Q(-1), Q(1, 2)).well_formed())
        self.assertIn("docket.malformed_schedule",
                      _codes(_run(EMPTY, [], [], schedules=(replace(SCHEDULE,
                                                                    threshold=Q(2)),))))
        # A query whose target does not bind the claim type's rule is not filed.
        stray = Query("q:9", "case:9", "ct:liable", 1, "other:x")
        self.assertIn("docket.query_not_well_formed",
                      _codes(_run(EMPTY, [], [], queries=(stray,))))

    def test_liabilities_are_exact_rationals(self):
        report = _run(EMPTY, [], [], horizon=3)
        self.assertEqual(report.total_liability, Q(3, 20))
        self.assertIsInstance(report.total_liability, Q)


if __name__ == "__main__":
    unittest.main()


from src.answerability import Discharge, Dispose, ProceduralClosure
from src.case_docket import (
    AdjudicationTransaction, LiabilityEntry, RefusalClock, case_stream_liabilities,
    merits_ledger_events, verify_transaction)

AUTH = "auth:review"


def _merits_bundle(query=QUERY, schedule=SCHEDULE, interval=POSITIVE):
    certificate = certify_merits(query, schedule, interval, f"cert:{query.query_id}")
    obligation = decision_obligation(query, f"e:file:{query.query_id}", 0)
    events = merits_ledger_events(query, certificate, 1, AUTH)
    ledger = LedgerLog("merits", (FileObligation(f"e:file:{query.query_id}", 0,
                                                 obligation),) + events)
    ruling = Ruling(f"ru:{query.query_id}", query.query_id,
                    schedule.positive_verdict if certificate.direction == "positive"
                    else schedule.negative_verdict, BASIS_MERITS,
                    (certificate.certificate_id,), interval.book_version,
                    schedule.schedule_version)
    transaction = AdjudicationTransaction(
        f"tx:{query.query_id}", query, schedule, f"d:{query.query_id}", BASIS_MERITS,
        RefusalClock(0, 0), ruling, certificate, interval,
        tuple(e.event_id for e in events), events[-1].event_id, ())
    return transaction, ledger


def _default_bundle(query=QUERY, schedule=SCHEDULE):
    obligation = decision_obligation(query, f"e:file:{query.query_id}", 0)
    ruling = Ruling(f"ru:{query.query_id}", query.query_id, schedule.fallback_verdict,
                    BASIS_DEFAULT, (), 1, schedule.schedule_version)
    closure, boundary = default_disposition(
        query, f"e:def:{query.query_id}", 1, AUTH, ruling_id=ruling.ruling_id,
        fallback_verdict=schedule.fallback_verdict)
    ledger = LedgerLog("default", (FileObligation(f"e:file:{query.query_id}", 0,
                                                  obligation), closure, boundary))
    transaction = AdjudicationTransaction(
        f"tx:{query.query_id}", query, schedule, f"d:{query.query_id}", BASIS_DEFAULT,
        RefusalClock(0, 0), ruling, None, None,
        (closure.event_id, boundary.event_id), boundary.event_id, ())
    return transaction, ledger


class AdjudicationTransactionTests(unittest.TestCase):
    """Result 1 (transaction completeness) and 2 (basis coherence)."""

    def test_merits_transaction_is_accepted_and_complete(self):
        transaction, ledger = _merits_bundle()
        report = verify_transaction(transaction, ledger)
        self.assertTrue(report.accepted, report.obstructions)
        self.assertEqual(report.basis, BASIS_MERITS)
        self.assertEqual(report.total_liability, Q(0))
        closed = verify_ledger(ledger).closed["d:q:1"]
        self.assertEqual(closed.closure_kind, "discharge")
        self.assertTrue(closed.coverage_events)

    def test_default_transaction_is_accepted_with_procedural_closure(self):
        transaction, ledger = _default_bundle()
        report = verify_transaction(transaction, ledger)
        self.assertTrue(report.accepted, report.obstructions)
        state = verify_ledger(ledger).closed["d:q:1"]
        # Result 3: procedural, never withdrawal, and no merits coverage.
        self.assertEqual(state.closure_kind, "procedural")
        self.assertNotEqual(state.closure_kind, "withdrawal")
        self.assertEqual(state.coverage_events, ())
        self.assertEqual(verify_ledger(ledger).coverage, ())
        self.assertEqual([e.kind for e in report.derived_liabilities], ["default"])
        self.assertEqual(report.total_liability, SCHEDULE.default_tariff)

    def test_decline_transaction_accrues_refusal_from_the_clock(self):
        obligation = decision_obligation(QUERY, "e:file", 0)
        ledger = LedgerLog("open", (FileObligation("e:file", 0, obligation),))
        snapshot = AdjudicationTransaction("tx:s", QUERY, SCHEDULE, "d:q:1", "decline",
                                           RefusalClock(0, 0))
        report = verify_transaction(snapshot, ledger)
        self.assertTrue(report.accepted, report.obstructions)
        # Result 6: an instantaneous snapshot has elapsed no time and costs nothing.
        self.assertEqual(report.total_liability, Q(0))
        longitudinal = replace(snapshot, clock=RefusalClock(0, 3))
        later = verify_transaction(longitudinal, ledger)
        self.assertTrue(later.accepted, later.obstructions)
        self.assertEqual(later.total_liability, 3 * SCHEDULE.refusal_tariff)
        self.assertEqual([e.step for e in later.derived_liabilities], [0, 1, 2])
        # A declared liability that is not the derived one is rejected.
        forged = replace(longitudinal, liabilities=(
            LiabilityEntry("refusal", "q:1", Q(0), 0),))
        self.assertIn("docket.liability_mismatch",
                      _codes(verify_transaction(forged, ledger)))

    def test_merits_mutations_are_each_rejected(self):
        transaction, ledger = _merits_bundle()
        self.assertTrue(verify_transaction(transaction, ledger).accepted)
        certificate, interval, ruling = (transaction.certificate, transaction.interval,
                                         transaction.ruling)
        mutations = {
            "wrong query": replace(transaction, ruling=replace(ruling, query_id="q:9")),
            "wrong obligation": replace(transaction, obligation_id="d:q:9"),
            "changed target": replace(transaction,
                                      query=replace(QUERY, target_instance="target:z")),
            "changed claim type": replace(
                transaction, query=replace(QUERY, claim_type_id="ct:other")),
            "changed schedule version": replace(
                transaction, schedule=replace(SCHEDULE, schedule_version=2)),
            "changed book version": replace(
                transaction, interval=replace(interval, book_version=9)),
            "changed interval target": replace(
                transaction, interval=replace(interval, target="target:z")),
            "borrowed certificate": replace(
                transaction, certificate=replace(certificate, query_id="q:2")),
            "certificate under another book": replace(
                transaction, certificate=replace(certificate, book_version=7)),
            "verdict mismatch": replace(
                transaction, ruling=replace(ruling, verdict="not-liable")),
            "basis mismatch": replace(
                transaction, ruling=replace(ruling, basis_tag=BASIS_DEFAULT)),
        }
        for label, mutant in mutations.items():
            report = verify_transaction(mutant, ledger)
            self.assertFalse(report.accepted, label)
            self.assertTrue(report.obstructions, label)

    def test_cross_basis_pairings_are_rejected(self):
        merits, merits_ledger = _merits_bundle()
        default, default_ledger = _default_bundle()
        # Merits ruling paired with a procedural closure.
        crossed = replace(merits, ledger_event_ids=(), boundary_event_id=None)
        report = verify_transaction(crossed, default_ledger)
        self.assertFalse(report.accepted)
        self.assertIn("docket.merits_without_discharge", _codes(report))
        # Merits ruling paired with a substantive withdrawal.
        obligation = decision_obligation(QUERY, "e:file:q:1", 0)
        withdrawn = LedgerLog("withdrawn", (
            FileObligation("e:file:q:1", 0, obligation),
            Dispose("e:wd", 1, "d:q:1", "withdrawal", "w:1", AUTH)))
        self.assertIn("docket.merits_without_discharge",
                      _codes(verify_transaction(replace(merits, ledger_event_ids=(),
                                                        boundary_event_id=None),
                                                withdrawn)))
        # Default ruling paired with a merits discharge.
        self.assertIn("docket.default_without_procedural_closure",
                      _codes(verify_transaction(
                          replace(default, ledger_event_ids=(), boundary_event_id=None),
                          merits_ledger)))
        # Default with a certificate, and default with the wrong fallback.
        self.assertIn("docket.default_citing_certificate",
                      _codes(verify_transaction(
                          replace(default, certificate=merits.certificate,
                                  ruling=replace(default.ruling,
                                                 certificate_ids=("cert:q:1",))),
                          default_ledger)))
        self.assertIn("docket.default_not_fallback",
                      _codes(verify_transaction(
                          replace(default, ruling=replace(default.ruling,
                                                          verdict="liable")),
                          default_ledger)))

    def test_a_default_cannot_enter_the_merits_channel(self):
        """Result 3: intrinsic, not a naming convention."""
        default, default_ledger = _default_bundle()
        # There is no constructor turning a ruling into a certificate; the only
        # route is certify_merits, which needs an interval clearing the threshold.
        self.assertIsNone(certify_merits(QUERY, SCHEDULE, EMPTY, "cert:x"))
        # Dressing the default's identifier as a certificate still fails, because
        # the direction is recomputed from the interval.
        dressed = MeritsCertificate(default.ruling.ruling_id, "q:1", "target:x", 1, 1,
                                    EMPTY, Q(3, 4), "positive")
        forged = AdjudicationTransaction(
            "tx:forge", QUERY, SCHEDULE, "d:q:1", BASIS_MERITS, RefusalClock(0, 0),
            replace(default.ruling, basis_tag=BASIS_MERITS, verdict="liable",
                    certificate_ids=(dressed.certificate_id,)),
            dressed, EMPTY, (), None, ())
        report = verify_transaction(forged, default_ledger)
        self.assertFalse(report.accepted)
        self.assertIn("docket.unsupported_merits", _codes(report))
        # And the procedural closure creates no coverage the ledger could reuse.
        self.assertEqual(verify_ledger(default_ledger).coverage, ())

    def test_missing_and_foreign_ledger_records_are_rejected(self):
        transaction, ledger = _merits_bundle()
        self.assertIn("docket.missing_ledger_event",
                      _codes(verify_transaction(
                          replace(transaction, ledger_event_ids=("e:nope",)), ledger)))
        other = decision_obligation(Query("q:2", "case:2", "ct:liable", 1, "target:x"),
                                    "e:file:q:2", 1)
        extended = LedgerLog("extended", ledger.events + (
            FileObligation("e:file:q:2", 1, other),))
        self.assertIn("docket.foreign_ledger_event",
                      _codes(verify_transaction(
                          replace(transaction,
                                  ledger_event_ids=("e:file:q:2",)), extended)))
        self.assertIn("docket.missing_boundary_disposition",
                      _codes(verify_transaction(
                          replace(transaction, boundary_event_id="e:file:q:1"), ledger)))

    def test_duplicate_identifiers_are_not_hidden_by_map_construction(self):
        report = adjudicate([QUERY, QUERY], [SCHEDULE], {"target:x": EMPTY}, [], [])
        self.assertIn("docket.duplicate_query", _codes(report))
        report = adjudicate([QUERY], [SCHEDULE, SCHEDULE], {"target:x": EMPTY}, [], [])
        self.assertIn("docket.duplicate_schedule", _codes(report))
        certificate = certify_merits(QUERY, SCHEDULE, POSITIVE, "cert:p")
        report = adjudicate([QUERY], [SCHEDULE], {"target:x": POSITIVE}, [],
                            [certificate, certificate])
        self.assertIn("docket.duplicate_certificate", _codes(report))
        ruling = Ruling("ru:1", "q:1", "not-liable", BASIS_DEFAULT, (), 1, 1)
        report = adjudicate([QUERY], [SCHEDULE], {"target:x": EMPTY}, [ruling, ruling], [])
        self.assertIn("docket.duplicate_ruling_id", _codes(report))

    def test_unruled_query_cannot_be_omitted_from_decline_accounting(self):
        second = Query("q:2", "case:2", "ct:liable", 1, "target:x")
        report = adjudicate([QUERY, second], [SCHEDULE], {"target:x": EMPTY},
                            [Ruling("ru:1", "q:1", "not-liable", BASIS_DEFAULT, (), 1, 1)],
                            [], filed_step=0, horizon_step=2)
        self.assertTrue(report.accepted, report.obstructions)
        refusal = [e for e in report.liabilities if e.kind == "refusal"]
        # q:2 was never mentioned by the caller and still accrues its charge.
        self.assertEqual({e.query_id for e in refusal}, {"q:2"})
        self.assertEqual(len(refusal), 2)
        self.assertEqual(report.open_decisions, ("q:2",))

    def test_case_stream_liability_interface(self):
        merits, merits_ledger = _merits_bundle()
        default, default_ledger = _default_bundle(
            Query("q:2", "case:1", "ct:liable", 1, "target:x"))
        obligation = decision_obligation(
            Query("q:3", "case:1", "ct:liable", 1, "target:x"), "e:file:q:3", 0)
        open_ledger = LedgerLog("open", (FileObligation("e:file:q:3", 0, obligation),))
        decline = AdjudicationTransaction(
            "tx:q:3", Query("q:3", "case:1", "ct:liable", 1, "target:x"), SCHEDULE,
            "d:q:3", "decline", RefusalClock(0, 4))
        reports = [verify_transaction(merits, merits_ledger),
                   verify_transaction(default, default_ledger),
                   verify_transaction(decline, open_ledger)]
        for report in reports:
            self.assertTrue(report.accepted, report.obstructions)
        stream = case_stream_liabilities(reports, horizon_step=4, open_decisions=("q:3",))
        self.assertEqual(stream.default_total, SCHEDULE.default_tariff)
        self.assertEqual(stream.refusal_total, 4 * SCHEDULE.refusal_tariff)
        self.assertEqual(stream.total, Q(1, 10) + Q(4, 20))
        self.assertEqual(stream.open_decisions, ("q:3",))
        self.assertEqual(len(stream.entries), 5)
