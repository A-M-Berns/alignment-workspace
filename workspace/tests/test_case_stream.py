from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path
import re
import unittest

from src.case_stream import (
    Arrival, ServiceCosts, SolvencyCoupling, StreamPolicy, StreamSchedule,
    aggregate_default_grounds, combine_liabilities, dates_in_arrears,
    default_resolution_rate, lower_density, merits_coverage, run_stream, trilemma)
from src.grammar import CATALOG_BY_ID, judge_objection

COSTS = ServiceCosts(Q(2), Q(1), Q(1, 2), Q(1))
SCHEDULE = StreamSchedule(Q(1, 20), Q(1, 10), Q(1, 2), 4)
SOLVENT = SolvencyCoupling(Q(100), True)
STREAM = tuple(Arrival(f"q:{d}", d, True) for d in range(8))

DECLINE = StreamPolicy("decline", 0, 0)
DEFAULT = StreamPolicy("default", 0, 2)
TRACK = StreamPolicy("track", 1, 0)


def _run(policy, arrivals=STREAM, horizon=8, coupling=SOLVENT, admission=True,
         costs=COSTS, schedule=SCHEDULE):
    return run_stream(arrivals, costs, schedule, policy, coupling, horizon,
                      admission=admission)


class CaseStreamTests(unittest.TestCase):
    # The ledger-completeness check moved to the consolidation, which now
    # owns the claim ledger and enforces coverage in its own runner.
    def test_all_accounting_is_exact_rational(self):
        report = _run(DECLINE)
        self.assertIsInstance(report.accumulated_liability, Q)
        for record in report.records:
            for value in (record.refusal_accrued, record.default_accrued,
                          record.accumulated):
                self.assertIsInstance(value, Q)

    def test_capacity_is_derived_from_declared_service_work(self):
        self.assertEqual(COSTS.ruling_capacity, 2)
        self.assertEqual(COSTS.admission_capacity, 2)
        # Capacity is a mechanism quantity, not a fresh parameter: halving the
        # per-date work halves what a date affords.
        halved = replace(COSTS, per_date_work=Q(1))
        self.assertEqual(halved.ruling_capacity, 1)

    # CS-J1: no free silence.
    def test_bounded_liability_bounds_the_dates_in_arrears(self):
        report = _run(DECLINE)
        self.assertGreater(report.accumulated_liability, Q(0))
        # Each date in arrears accrues at least one refusal tariff unit, so the
        # accumulated liability bounds the arrears count exactly.
        self.assertLessEqual(
            Q(dates_in_arrears(report)),
            report.accumulated_liability / SCHEDULE.refusal_tariff)
        # Silence is strictly costly: never ruling leaves every arrival open.
        self.assertEqual(report.open_at_end, len(STREAM))
        self.assertEqual(report.rulings_total, 0)
        # Tracking the stream costs nothing in refusal.
        tracked = _run(TRACK)
        self.assertEqual(tracked.accumulated_liability, Q(0))
        self.assertEqual(tracked.open_at_end, 0)
        self.assertEqual(dates_in_arrears(tracked), 0)

    def test_liability_grows_without_bound_under_persistent_silence(self):
        short, long = _run(DECLINE, horizon=4), _run(DECLINE, horizon=8)
        self.assertGreater(long.accumulated_liability, short.accumulated_liability)
        # Quadratic in the horizon: the open set itself grows each date.
        longer = run_stream(tuple(Arrival(f"q:{d}", d, True) for d in range(16)),
                            COSTS, SCHEDULE, DECLINE, SOLVENT, 16)
        self.assertGreater(longer.accumulated_liability,
                           2 * long.accumulated_liability)

    # CS-J2: the trilemma.
    def test_at_least_one_trilemma_branch_holds_for_every_policy(self):
        bound = Q(1, 2)
        for policy in (DECLINE, DEFAULT, TRACK):
            verdict = trilemma(_run(policy), bound)
            self.assertTrue(verdict.holds, policy.policy_id)
        # And the branches separate the three policies.
        self.assertTrue(trilemma(_run(DECLINE), bound).unbounded_liability)
        self.assertFalse(trilemma(_run(DECLINE), bound).rate_matches)
        self.assertTrue(trilemma(_run(TRACK), bound).rate_matches)
        self.assertFalse(trilemma(_run(TRACK), bound).unbounded_liability)
        # Defaults among the rulings are exactly counted.
        self.assertEqual(trilemma(_run(DEFAULT), bound).defaults_counted,
                         _run(DEFAULT).defaults_total)

    def test_insolvency_is_the_second_branch(self):
        thin = SolvencyCoupling(Q(1, 4), True)
        report = _run(DECLINE, coupling=thin)
        self.assertIsNotNone(report.insolvency_date)
        self.assertTrue(trilemma(report, Q(100)).insolvent)
        self.assertTrue(trilemma(report, Q(100)).holds)

    # CS-N1: necessity of the solvency coupling.
    def test_without_the_coupling_liability_accumulates_without_consequence(self):
        uncoupled = SolvencyCoupling(Q(0), False)
        report = _run(DECLINE, coupling=uncoupled)
        # Every other hypothesis is in force: positive arrivals, bounded capacity,
        # positive tariffs.  Liability still accrues...
        self.assertGreater(report.accumulated_liability, Q(0))
        self.assertGreater(lower_density(STREAM, 8), Q(0))
        # ...and nothing whatever follows from it.
        self.assertIsNone(report.insolvency_date)
        self.assertFalse(trilemma(report, Q(100)).insolvent)
        # With the coupling and the same stream, the trigger fires.
        self.assertIsNotNone(_run(DECLINE, coupling=SolvencyCoupling(Q(1, 4))).insolvency_date)

    # CS-N2: necessity of admission.
    def test_without_admission_a_flood_defeats_every_policy(self):
        flood = tuple(Arrival(f"f:{i}", 0, True) for i in range(50))
        unadmitted = _run(TRACK, arrivals=flood, admission=False)
        admitted = _run(TRACK, arrivals=flood, admission=True)
        # Unadmitted: all 50 open from date 0 against a capacity of 1 merits/date.
        self.assertEqual(unadmitted.records[0].open_after, 49)
        self.assertGreater(unadmitted.accumulated_liability,
                           admitted.accumulated_liability)
        # Admission bounds the live set: at most `admission_capacity` per date.
        for record in admitted.records:
            self.assertLessEqual(len(record.admitted), COSTS.admission_capacity)
        self.assertLessEqual(admitted.records[0].open_after,
                             COSTS.admission_capacity)
        # The finite-live-state discipline holds only under admission.
        self.assertGreater(unadmitted.records[0].open_after,
                           admitted.records[0].open_after)

    # CS-J3: fairness floor.
    def test_finite_overtaking_admission_defers_nothing_forever(self):
        burst = tuple(Arrival(f"b:{i}", 0, True) for i in range(6))
        report = _run(DECLINE, arrivals=burst, horizon=8)
        # Every query is admitted within a finite wait, so every clock runs.
        self.assertEqual(report.never_admitted, ())
        self.assertEqual(report.admitted_total, len(burst))
        self.assertLessEqual(report.max_wait,
                             len(burst) // COSTS.admission_capacity + 1)

    # CS-J4: the aggregate-default objection.
    def test_always_default_closes_everything_and_maximizes_the_metric(self):
        report = _run(DEFAULT)
        # Every case obligation terminates.
        self.assertEqual(report.open_at_end, 0)
        self.assertEqual(report.defaults_total, len(STREAM))
        self.assertEqual(report.rulings_total, 0)
        # The metric hits its maximum and merits coverage its minimum.
        self.assertEqual(default_resolution_rate(report, STREAM), Q(1))
        self.assertEqual(merits_coverage(report, STREAM), Q(0))
        # Which generates filable grounds against the book's declared bound.
        grounds = aggregate_default_grounds(report, STREAM, SCHEDULE, "g:agg")
        self.assertIsNotNone(grounds)
        self.assertEqual(grounds.payload["rate"], Q(1))
        self.assertEqual(grounds.payload["bound"], Q(1, 2))
        # Always-decline fails the trilemma's third branch outright.
        self.assertFalse(trilemma(_run(DECLINE), Q(1, 2)).rate_matches)
        # Tracking generates no grounds.
        self.assertIsNone(aggregate_default_grounds(_run(TRACK), STREAM, SCHEDULE, "g"))
        # With no declared bound there is no standard, hence no grounds.
        self.assertIsNone(aggregate_default_grounds(
            report, STREAM, replace(SCHEDULE, declared_default_rate_bound=None), "g"))

    def test_the_rate_window_is_book_content_not_canonical(self):
        """P4: window choice is load-bearing, and the honest fix is that it is
        itself objectionable book content."""
        report = _run(DEFAULT)
        narrow = aggregate_default_grounds(report, STREAM,
                                           replace(SCHEDULE, rate_window=1), "g1")
        wide = aggregate_default_grounds(report, STREAM,
                                         replace(SCHEDULE, rate_window=8), "g2")
        self.assertIsNotNone(narrow)
        self.assertIsNotNone(wide)
        # Different windows yield different grounds payloads, so the window is
        # load-bearing; neither is canonical, and both are declared book content.
        self.assertNotEqual(narrow.payload["window"], wide.payload["window"])
        # A book that declares a bound of 1 is never objectionable on this ground,
        # which is exactly why the bound is itself challengeable content.
        self.assertIsNone(aggregate_default_grounds(
            report, STREAM, replace(SCHEDULE, declared_default_rate_bound=Q(1)), "g"))

    # B4: the attack suite.
    def test_capacity_starvation_by_nonsubstantive_filings_is_bounded(self):
        noise = tuple(Arrival(f"n:{i}", 0, False) for i in range(20))
        report = _run(TRACK, arrivals=noise, horizon=8)
        # Admission caps the live set regardless of how much is filed.
        self.assertEqual(report.substantive_admitted, 0)
        for record in report.records:
            self.assertLessEqual(len(record.admitted), COSTS.admission_capacity)

    def test_extraction_siege_and_case_stream_compose_without_double_counting(self):
        """P6: the no-double-counting lemma."""
        report = _run(DECLINE)
        charges = {("objection:o1", date): Q(1, 10) for date in range(8)}
        combined = combine_liabilities(charges, report)
        self.assertTrue(combined.disjoint)
        self.assertEqual(combined.total,
                         combined.charge_total + combined.tariff_total)
        self.assertEqual(combined.tariff_total, report.accumulated_liability)
        # Charges and tariffs are keyed on different coordinates, so no event is
        # counted twice; a forged key collision is detected.
        collided = dict(charges)
        collided[("docket", 0)] = Q(1)
        self.assertFalse(combine_liabilities(collided, report).disjoint)

    def test_patron_funded_decline_pays_liability_but_does_not_erase_it(self):
        report = _run(DECLINE)
        subsidised = SolvencyCoupling(report.accumulated_liability + Q(1), True)
        funded = _run(DECLINE, coupling=subsidised)
        # A patron can move the insolvency branch out of reach...
        self.assertIsNone(funded.insolvency_date)
        # ...but the accrued liability and the open obligations are unchanged.
        self.assertEqual(funded.accumulated_liability, report.accumulated_liability)
        self.assertEqual(funded.open_at_end, report.open_at_end)
        self.assertFalse(trilemma(funded, Q(1, 2)).rate_matches)
        self.assertTrue(trilemma(funded, Q(1, 2)).holds)


from src.case_stream import (
    FENCED, POOLED, PATRON_TRANSFER, Fence, Transfer, cross_subsidy_grounds,
    crosses_fence)
from src.grammar import CATALOG_BY_ID, judge_objection as _judge


class PatronFenceTests(unittest.TestCase):
    """T6: patron-funded decline, resolved by reuse of the cross-subsidy objection."""

    def test_fenced_instance_fires_and_pooled_instance_does_not(self):
        self.assertTrue(crosses_fence(PATRON_TRANSFER, FENCED))
        self.assertFalse(crosses_fence(PATRON_TRANSFER, POOLED))
        fenced = cross_subsidy_grounds(PATRON_TRANSFER, FENCED, "g:fenced")
        pooled = cross_subsidy_grounds(PATRON_TRANSFER, POOLED, "g:pooled")
        self.assertIsNotNone(fenced)
        self.assertIsNone(pooled)
        self.assertEqual(fenced.payload["fence_id"], "fence:mechanism")
        self.assertEqual(fenced.payload["amount"], Q(1))

    def test_it_reuses_the_existing_objection_type_with_a_declared_footprint(self):
        objection = CATALOG_BY_ID["cross-subsidy"]
        self.assertEqual(sorted(objection.footprint.declared), ["liabilities"])
        self.assertEqual(objection.footprint.standard_tables, ())
        grounds = cross_subsidy_grounds(PATRON_TRANSFER, FENCED, "g")
        verdict = _judge(objection, {"liabilities": {"t:patron": Q(1)}}, grounds)
        self.assertTrue(verdict.accepted, verdict.obstructions)
        self.assertTrue(verdict.upheld)
        # The judge is enforced like every other: an undeclared read fails.
        leaky = replace(objection, judge=lambda access, g: bool(access.read("rulings")))
        self.assertFalse(_judge(leaky, {"rulings": {}}, grounds).accepted)

    def test_a_transfer_inside_one_side_of_the_fence_does_not_cross(self):
        internal = Transfer("t:internal", "account:mechanism", "account:mechanism", Q(1))
        self.assertFalse(crosses_fence(internal, FENCED))
        self.assertIsNone(cross_subsidy_grounds(internal, FENCED, "g"))
        # An undeclared fence never charges, however the accounts are arranged.
        undeclared = Fence("fence:latent", ("account:mechanism",), declared=False)
        self.assertFalse(crosses_fence(PATRON_TRANSFER, undeclared))

    def test_the_trilemma_statement_is_untouched_by_the_patron(self):
        report = _run(DECLINE)
        subsidised = _run(DECLINE, coupling=SolvencyCoupling(
            report.accumulated_liability + Q(1), True))
        self.assertIsNone(subsidised.insolvency_date)
        self.assertEqual(subsidised.accumulated_liability,
                         report.accumulated_liability)
        self.assertFalse(trilemma(subsidised, Q(1, 2)).rate_matches)
        self.assertTrue(trilemma(subsidised, Q(1, 2)).holds)

if __name__ == "__main__":
    unittest.main()
